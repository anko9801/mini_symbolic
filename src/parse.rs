use crate::project;
use std::collections::HashMap;
use z3::ast::Ast;
use Operand::*;
use Operation::*;
use Register::*;

#[derive(Debug, Clone, Copy)]
enum Operation {
    mov,
    add,
    sub,
    imul,
    idiv,
    cdq,
    cmp,
    inc,
    dec,
    jnz,
    jne,
    jz,
    je,
    jl,
    jg,
    ret,
    nop,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum Register {
    rax,
    rbx,
    rcx,
    rdx,
    rsi,
    rdi,
    r12,
    rbp,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum Flag {
    ZF,
    SF,
    OF,
}

#[derive(Debug, Clone, Copy)]
pub enum Operand {
    ImmVal(i64),
    Reg(Register),
}

#[derive(Debug, Clone, Copy)]
struct Instruction {
    offset: usize,
    size: usize,
    op: Operation,
    dst: Option<Operand>,
    src: Option<Operand>,
}
impl Instruction {
    fn new(
        offset: usize,
        size: usize,
        op: Operation,
        dst: Option<Operand>,
        src: Option<Operand>,
    ) -> Instruction {
        Instruction {
            offset,
            size,
            op,
            dst,
            src,
        }
    }
}

pub struct Code<'ctx> {
    insts: Vec<Instruction>,
    // solver: Rc<RefCell<arch::x86<'ctx>>>,
    init_state: HashMap<Register, Option<i64>>,
    end_state: HashMap<Register, Option<i64>>,
    find: Vec<usize>,
    avoid: Vec<usize>,
    insts_index: HashMap<usize, Instruction>,
    pub project: project::Project<'ctx>,
    pub registers: HashMap<Register, z3::ast::BV<'ctx>>,
    init_regs: HashMap<Register, z3::ast::BV<'ctx>>,
    pub cflags: HashMap<Flag, z3::ast::Bool<'ctx>>,
    // z3のAPIにassertionsが定義されていないためまだ
    // active_state: VecDeque<Box<z3::ast::Ast>>,
    // insts_index = {}        # instructions index by address
}

// b: rdi/r12, t: rdx, e: rbp, p: rbx, i: rcx,
//         cmp     r12, 1
//         je      .fail
//         mov     rax, r12
//         imul    rax, r12
//         cdq
//         idiv    rbx
//         mov     rax, rdx
//         cmp     rdx, 1
//         je      .fail
//         cmp     rbp, 2
//         je      .fail
//         mov     rcx, 2
// .L5:
//         imul    eax, eax
//         cdq
//         idiv    ebx
//         mov     eax, edx
//         cmp     edx, 1
//         je      .fail
//         add     ecx, 1
//         cmp     ecx, ebp
//         jne     .L5
// .fail:
//         ret

impl<'ctx> Code<'ctx> {
    pub fn new(context: &'ctx z3::Context) -> Self {
        let project = project::Project::new(context, 64);
        let registers = HashMap::from([
            (Register::rax, project.get_int_with_ctx(context, "init_rax")),
            (Register::rbx, project.get_int_with_ctx(context, "init_rbx")),
            (Register::rcx, project.get_int_with_ctx(context, "init_rcx")),
            (Register::rdx, project.get_int_with_ctx(context, "init_rdx")),
            (Register::rsi, project.get_int_with_ctx(context, "init_rsi")),
            (Register::rdi, project.get_int_with_ctx(context, "init_rdi")),
            (Register::rbp, project.get_int_with_ctx(context, "init_rbp")),
            (Register::r12, project.get_int_with_ctx(context, "init_r12")),
        ]);
        let init_regs = registers.clone();
        let cflags = HashMap::from([
            (Flag::ZF, project.get_bool_with_ctx(context, "ZF")),
            (Flag::SF, project.get_bool_with_ctx(context, "SF")),
            (Flag::OF, project.get_bool_with_ctx(context, "OF")),
        ]);
        let mut parent = Self {
            insts: vec![
                Instruction::new(0x0, 1, cmp, Some(Reg(rbx)), Some(ImmVal(1))),
                Instruction::new(0x0, 1, cmp, Some(Reg(r12)), Some(ImmVal(1))),
                Instruction::new(0x1, 1, je, Some(ImmVal(19)), None),
                Instruction::new(0x2, 1, mov, Some(Reg(rax)), Some(Reg(r12))),
                Instruction::new(0x3, 1, imul, Some(Reg(rax)), Some(Reg(r12))),
                Instruction::new(0x4, 1, cdq, None, None),
                Instruction::new(0x5, 1, idiv, Some(Reg(rbx)), None),
                Instruction::new(0x6, 1, mov, Some(Reg(rax)), Some(Reg(rdx))),
                Instruction::new(0x7, 1, cmp, Some(Reg(rdx)), Some(ImmVal(1))),
                Instruction::new(0x8, 1, je, Some(ImmVal(12)), None),
                Instruction::new(0x9, 1, cmp, Some(Reg(rbp)), Some(ImmVal(2))),
                Instruction::new(0xa, 1, je, Some(ImmVal(10)), None),
                Instruction::new(0xb, 1, mov, Some(Reg(rcx)), Some(ImmVal(2))),
                // Loop
                Instruction::new(0xc, 1, imul, Some(Reg(rax)), Some(Reg(rax))),
                Instruction::new(0xd, 1, cdq, None, None),
                Instruction::new(0xe, 1, idiv, Some(Reg(rbx)), None),
                Instruction::new(0xf, 1, mov, Some(Reg(rax)), Some(Reg(rdx))),
                Instruction::new(0x10, 1, cmp, Some(Reg(rdx)), Some(ImmVal(1))),
                Instruction::new(0x11, 1, je, Some(ImmVal(3)), None),
                Instruction::new(0x12, 1, add, Some(Reg(rcx)), Some(ImmVal(1))),
                Instruction::new(0x13, 1, cmp, Some(Reg(rcx)), Some(Reg(rbp))),
                Instruction::new(0x14, 1, jne, Some(ImmVal(-9)), None),
                // fail
                Instruction::new(0x15, 1, ret, None, None),
                // Instruction::new(0x0, 4, cmp, Some(Reg(rsi)), Some(ImmVal(1))),
                // Instruction::new(0x4, 2, jl, Some(ImmVal(8)), None), // 0x4 + 2 + 8 = 0xe
                // Instruction::new(0x6, 3, add, Some(Reg(rdx)), Some(Reg(rdx))),
                // Instruction::new(0x9, 3, dec, Some(Reg(rsi)), None),
                // Instruction::new(0xc, 2, jnz, Some(ImmVal(-8)), None), // 0xc + 2 - 8 = 0x6
                // Instruction::new(0xe, 3, cmp, Some(Reg(rdx)), Some(Reg(rax))),
                // Instruction::new(0x11, 2, je, Some(ImmVal(1)), None), // 0x11 + 2 + 1 = 0x14
                // Instruction::new(0x13, 1, ret, None, None),
                // Instruction::new(0x14, 1, nop, None, None),
            ],
            init_state: HashMap::from([
                (Register::rax, None),
                (Register::rbx, Some(185)), //
                (Register::rcx, None),
                (Register::rdx, None),
                (Register::rsi, None),
                (Register::rdi, None),
                (Register::rbp, None),
                (Register::r12, None),
            ]),
            end_state: HashMap::from([
                (Register::rax, None),
                (Register::rbx, None),
                (Register::rcx, None),
                (Register::rdx, None),
                (Register::rsi, None),
                (Register::rdi, None),
                (Register::rbp, None),
                (Register::r12, None),
            ]),
            find: vec![],
            avoid: vec![0x15],
            // active_state: VecDeque::new(),
            insts_index: HashMap::new(),
            project,
            registers,
            init_regs,
            cflags,
        };
        for inst in parent.insts.clone() {
            parent.insts_index.insert(inst.offset, inst);
        }
        parent
    }

    pub fn print_insts(&self) {
        println!("[*] symbolic execute following instructions:");
        for inst in &self.insts {
            inst.print_inst();
        }
    }

    pub fn solve(&mut self) {
        self.print_insts();
        self.initialize(&self.init_state);
        self.gen_inst(0);
        println!("{:?}", self.project.solve());
        // self.solver.project.solver;
    }

    pub fn gen_inst(&mut self, offset: usize) -> Option<()> {
        match self.insts_index.get(&offset) {
            Some(inst) => {
                inst.print_inst();
                self.inc_id();
                let next = inst.offset + inst.size;
                let is_find = self.find.iter().find(|&&x| x == inst.offset).is_some();
                let is_avoid = self.avoid.iter().find(|&&x| x == inst.offset).is_some();
                let mut jump_flag = true;
                match inst.op {
                    add => {
                        self.inst_add(inst.dst?, inst.src?);
                    }
                    sub => {
                        self.inst_sub(inst.dst?, inst.src?);
                    }
                    imul => {
                        self.inst_imul(inst.dst?, inst.src?);
                    }
                    idiv => {
                        self.inst_idiv(inst.dst?);
                    }
                    cmp => {
                        self.inst_cmp(inst.dst?, inst.src?);
                    }
                    mov => {
                        self.inst_mov(inst.dst?, inst.src?);
                    }
                    inc => {
                        self.inst_inc(inst.dst?);
                    }
                    dec => {
                        self.inst_dec(inst.dst?);
                    }
                    jl => {
                        if let Some(ImmVal(val)) = inst.dst {
                            let jump = (next as i64 + val) as usize;
                            if let None = self.inst_jl(jump) {
                                jump_flag = false;
                            }
                        }
                    }
                    jg => {
                        if let Some(ImmVal(val)) = inst.dst {
                            let jump = (next as i64 + val) as usize;
                            if let None = self.inst_jg(jump) {
                                jump_flag = false;
                            }
                        }
                    }
                    jz | je => {
                        if let Some(ImmVal(val)) = inst.dst {
                            let jump = (next as i64 + val) as usize;
                            if let None = self.inst_jz(jump) {
                                jump_flag = false;
                            }
                        }
                    }
                    jnz | jne => {
                        if let Some(ImmVal(val)) = inst.dst {
                            let jump = (next as i64 + val) as usize;
                            if let None = self.inst_jnz(jump) {
                                jump_flag = false;
                            }
                        }
                    }
                    ret => {}
                    nop | cdq => {}
                    _ => {
                        unimplemented!();
                    }
                };
                if is_avoid {
                    return None;
                }
                if !jump_flag || self.project.generate_id() >= 39 || is_find {
                    self.result(&self.end_state);
                    loop {
                        let result = self.project.solve();
                        match result {
                            Some(model) => {
                                for (reg, var) in &self.init_regs {
                                    let val = model.eval(var, false);
                                    println!("\n{:?}: {:?}", reg, val);
                                    match val {
                                        Some(val) => {
                                            if *var == val {
                                                continue;
                                            }
                                            self.project.insert(&(*var)._eq(&val).not());
                                        }
                                        None => {
                                            break;
                                        }
                                    }
                                }
                            }
                            None => {
                                break;
                            }
                        };
                    }
                    return Some(());
                }
                return self.gen_inst(next);
            }
            None => {}
        };
        Some(())
    }
}

impl<'ctx> Instruction {
    fn print_inst(&self) {
        print!("{:?} ", self.op);
        if let Some(operand) = self.dst {
            match operand {
                ImmVal(val) => print!("{:?}", val),
                Reg(reg) => print!("{:?}", reg),
            };
        }
        if let Some(operand) = self.src {
            match operand {
                ImmVal(val) => print!(", {:?}", val),
                Reg(reg) => print!(", {:?}", reg),
            };
        }
        println!();
    }
}
