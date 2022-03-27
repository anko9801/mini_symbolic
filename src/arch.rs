use std::collections::HashMap;
use z3::{ast::Ast, SatResult};

use crate::parse::{Code, Flag, Operand, Register};

pub trait Arch {
    fn inst_add(&self, dst: isize, src: isize);
}

impl<'ctx> Code<'ctx> {
    pub fn initialize(&self, init_state: &HashMap<Register, Option<i64>>) {
        for (reg, state) in init_state {
            if let Some(val) = state {
                let val = self.project.get_const_int(*val);
                let reg = self.get_register(reg);
                self.project.insert(&reg._eq(&val));
            } else {
                let reg = self.get_register(reg);
                self.project
                    .insert(&reg.bvslt(&self.project.get_const_int(200)));
            }
        }
    }

    pub fn result(&self, end_state: &HashMap<Register, Option<i64>>) {
        for (reg, state) in end_state {
            if let Some(val) = state {
                let val = self.project.get_const_int(*val);
                let reg = self.get_register(reg);
                self.project.insert(&reg._eq(&val));
            }
        }
    }

    fn get_operand(&self, op: &Operand) -> z3::ast::BV {
        match op {
            Operand::ImmVal(val) => self.get_immval(*val),
            Operand::Reg(reg) => self.get_register(reg).clone(),
        }
    }

    pub fn get_register(&self, reg: &Register) -> &z3::ast::BV {
        &self.registers[reg]
    }

    pub fn get_cflag(&self, reg: &Flag) -> &z3::ast::Bool {
        &self.cflags[reg]
    }

    pub fn get_immval(&self, val: i64) -> z3::ast::BV {
        self.project.get_const_int(val)
    }

    pub fn store_register(
        registers: &mut HashMap<Register, z3::ast::BV<'ctx>>,
        dst: &Operand,
        val: z3::ast::BV<'ctx>,
    ) {
        match dst {
            Operand::ImmVal(_) => {}
            Operand::Reg(reg) => {
                registers.insert(*reg, val);
            }
        }
    }

    pub fn store_flag(
        cflags: &mut HashMap<Flag, z3::ast::Bool<'ctx>>,
        dst: &Flag,
        val: z3::ast::Bool<'ctx>,
    ) {
        cflags.insert(*dst, val);
    }

    pub fn inc_id(&self) {
        self.project.inc_id();
    }

    pub fn inst_mov(&self, dst: Operand, src: Operand) -> z3::ast::BV {
        let src = self.get_operand(&src);
        let res = self.project.get_int("bv_mov_res");
        self.project.insert(&res._eq(&src));
        res
    }

    pub fn inst_add(&mut self, dst: Operand, src: Operand) -> z3::ast::BV {
        let dst_var = self.get_operand(&dst);
        let src_var = self.get_operand(&src);
        let ctx = self.project.context;
        let res = self.project.get_int_with_ctx(ctx, "bv_add_res");

        self.project.insert(&(src_var + dst_var)._eq(&res));

        self.change_flag_from_result(&res);
        Self::store_register(&mut self.registers, &dst, res.clone());
        res
    }

    pub fn inst_sub(&mut self, dst: Operand, src: Operand) -> z3::ast::BV {
        let dst_var = self.get_operand(&dst);
        let src_var = self.get_operand(&src);
        let ctx = self.project.context;
        let res = self.project.get_int_with_ctx(ctx, "bv_sub_res");

        // dst - src == res
        self.project.insert(&(dst_var - src_var)._eq(&res));

        self.change_flag_from_result(&res);
        Self::store_register(&mut self.registers, &dst, res.clone());
        res
    }

    pub fn inst_imul(&mut self, dst: Operand, src: Operand) -> z3::ast::BV {
        let dst_var = self.get_operand(&dst);
        let src_var = self.get_operand(&src);
        let ctx = self.project.context;
        let res = self.project.get_int_with_ctx(ctx, "bv_mul_res");

        // dst * src == res
        self.project.insert(&(dst_var * src_var)._eq(&res));

        self.change_flag_from_result(&res);
        Self::store_register(&mut self.registers, &dst, res.clone());
        res
    }

    pub fn inst_idiv(&mut self, src: Operand) -> (z3::ast::BV, z3::ast::BV) {
        let ctx = self.project.context;
        let div = self.project.get_int_with_ctx(ctx, "bv_div_res");
        let rem = self.project.get_int_with_ctx(ctx, "bv_rem_res");
        {
            let dst_var = self.get_operand(&Operand::Reg(Register::rax));
            let src_var = self.get_operand(&src);

            // dst / src == div
            // dst % src == rem
            self.project.insert(&dst_var.bvsdiv(&src_var)._eq(&div));
            self.project.insert(&dst_var.bvsrem(&src_var)._eq(&rem));
        }

        self.change_flag_from_result(&div);
        Self::store_register(
            &mut self.registers,
            &Operand::Reg(Register::rax),
            div.clone(),
        );
        Self::store_register(
            &mut self.registers,
            &Operand::Reg(Register::rdx),
            rem.clone(),
        );
        (div, rem)
    }

    pub fn inst_cmp(&mut self, dst: Operand, src: Operand) {
        let dst_var = self.get_operand(&dst);
        let src_var = self.get_operand(&src);
        let ctx = self.project.context;
        let res = self.project.get_int_with_ctx(ctx, "bv_cmp_res");

        // dst - src == res
        self.project.insert(&(dst_var - src_var)._eq(&res));

        self.change_flag_from_result(&res);
    }

    pub fn inst_inc(&mut self, dst: Operand) -> z3::ast::BV {
        let dst_var = self.get_operand(&dst);
        let one = self.project.get_const_int(1);
        let ctx = self.project.context;
        let res = self.project.get_int_with_ctx(ctx, "bv_inc_res");

        // dst + 1 == res
        self.project.insert(&(dst_var + one)._eq(&res));

        self.change_flag_from_result(&res);
        Self::store_register(&mut self.registers, &dst, res.clone());
        res
    }

    pub fn inst_dec(&mut self, dst: Operand) -> z3::ast::BV {
        let dst_var = self.get_operand(&dst);
        let one = self.project.get_const_int(1);
        let ctx = self.project.context;
        let res = self.project.get_int_with_ctx(ctx, "bv_dec_res");

        // dst - 1 == res
        self.project.insert(&(dst_var - one)._eq(&res));

        self.change_flag_from_result(&res);
        Self::store_register(&mut self.registers, &dst, res.clone());
        res
    }

    pub fn change_flag_from_result(&mut self, res: &z3::ast::BV) {
        let ctx = self.project.context;

        let ZF = self.project.get_bool_with_ctx(ctx, "ZF");
        let SF = self.project.get_bool_with_ctx(ctx, "SF");
        let OF = self.project.get_bool_with_ctx(ctx, "OF");
        let zero = self.project.get_const_int(0);
        let cFalse = self.project.get_const_bool(false);

        // (res == 0) == ZF, (res < 0) == SF, OF == False
        self.project.insert(&res._eq(&zero)._eq(&ZF));
        self.project.insert(&res.bvslt(&zero)._eq(&SF));
        self.project.insert(&OF._eq(&cFalse));

        Self::store_flag(&mut self.cflags, &Flag::ZF, ZF.clone());
        Self::store_flag(&mut self.cflags, &Flag::SF, SF.clone());
        Self::store_flag(&mut self.cflags, &Flag::OF, OF.clone());
    }

    pub fn inst_jz(&mut self, jump_offset: usize) -> Option<()> {
        let cflags = self.cflags.clone();
        let registers = self.registers.clone();
        {
            let ZF = self.get_cflag(&Flag::ZF);
            let cTrue = self.project.get_const_bool(true);

            // ZF == True
            self.project.solver.push();
            self.project.insert(&ZF._eq(&cTrue));
        }
        if self.project.solver.check() == SatResult::Sat {
            println!("True jump to {}", jump_offset);
            self.gen_inst(jump_offset);
        }

        self.cflags = cflags;
        self.registers = registers;
        {
            let ZF = self.get_cflag(&Flag::ZF);
            let cFalse = self.project.get_const_bool(false);

            // ZF == False
            self.project.solver.pop(1);
            self.project.insert(&ZF._eq(&cFalse));
        }
        if self.project.solver.check() == SatResult::Sat {
            println!("False jump");
            return Some(());
        }
        None
    }

    pub fn inst_jnz(&mut self, jump_offset: usize) -> Option<()> {
        let cflags = self.cflags.clone();
        let registers = self.registers.clone();
        {
            let ZF = self.get_cflag(&Flag::ZF);
            let cFalse = self.project.get_const_bool(false);

            // ZF == False
            self.project.solver.push();
            self.project.insert(&ZF._eq(&cFalse));
        }
        if self.project.solver.check() == SatResult::Sat {
            println!("True jump to {}", jump_offset);
            self.gen_inst(jump_offset);
        }

        self.cflags = cflags;
        self.registers = registers;
        {
            let ZF = self.get_cflag(&Flag::ZF);
            let cTrue = self.project.get_const_bool(true);

            // ZF == True
            self.project.solver.pop(1);
            self.project.insert(&ZF._eq(&cTrue));
        }
        if self.project.solver.check() == SatResult::Sat {
            println!("False jump");
            return Some(());
        }
        None
    }

    pub fn inst_jg(&mut self, jump_offset: usize) -> Option<()> {
        let cflags = self.cflags.clone();
        let registers = self.registers.clone();
        {
            let ZF = self.get_cflag(&Flag::ZF);
            let SF = self.get_cflag(&Flag::SF);
            let OF = self.get_cflag(&Flag::OF);
            let cFalse = self.project.get_const_bool(false);
            let ctx = self.project.context;

            // ZF == False && SF == OF
            self.project.solver.push();
            self.project.insert(&z3::ast::Bool::and(
                ctx,
                &[&ZF._eq(&cFalse), (&SF._eq(&OF))],
            ));
        }
        if self.project.solver.check() == SatResult::Sat {
            println!("True jump to {}", jump_offset);
            self.gen_inst(jump_offset);
        }

        self.cflags = cflags;
        self.registers = registers;
        {
            let ZF = self.get_cflag(&Flag::ZF);
            let SF = self.get_cflag(&Flag::SF);
            let OF = self.get_cflag(&Flag::OF);
            let cTrue = self.project.get_const_bool(true);
            let ctx = self.project.context;

            // ZF == True || SF != OF
            self.project.solver.pop(1);
            self.project.insert(&z3::ast::Bool::or(
                ctx,
                &[&ZF._eq(&cTrue), (&SF._eq(&OF.not()))],
            ));
        }
        // TODO: False jumpしない場合jumpしない
        if self.project.solver.check() == SatResult::Sat {
            println!("False jump");
            return Some(());
        }
        None
    }

    pub fn inst_jl(&mut self, jump_offset: usize) -> Option<()> {
        let cflags = self.cflags.clone();
        let registers = self.registers.clone();
        {
            let SF = self.get_cflag(&Flag::SF);
            let OF = self.get_cflag(&Flag::OF);

            // SF != OF
            self.project.solver.push();
            self.project.insert(&SF._eq(&OF.not()));
        }
        if self.project.solver.check() == SatResult::Sat {
            println!("True jump to {}", jump_offset);
            self.gen_inst(jump_offset);
        }

        self.cflags = cflags;
        self.registers = registers;
        {
            let SF = self.get_cflag(&Flag::SF);
            let OF = self.get_cflag(&Flag::OF);

            // SF == OF
            self.project.solver.pop(1);
            self.project.insert(&SF._eq(&OF));
        }
        if self.project.solver.check() == SatResult::Sat {
            println!("False jump");
            return Some(());
        }
        None
    }
}
