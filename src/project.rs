use std::cell::RefCell;
use z3::{
    ast::{Bool, Int, BV},
    SatResult,
};

pub struct Project<'ctx> {
    pub context: &'ctx z3::Context,
    pub solver: z3::Solver<'ctx>,
    pub id: RefCell<usize>,
    pub is_finish: bool,
    bits: u32,
}

impl<'ctx> Project<'ctx> {
    pub fn new(context: &'ctx z3::Context, bits: u32) -> Self {
        let solver = z3::Solver::new(context);
        Project {
            context,
            solver,
            id: RefCell::new(0),
            is_finish: false,
            bits,
        }
    }

    pub fn inc_id(&self) {
        *self.id.borrow_mut() += 1;
    }

    pub fn generate_id(&self) -> usize {
        // let mut id = self.id.borrow_mut();
        // *id += 1;
        *self.id.borrow()
    }

    pub fn get_int(&self, name: &str) -> z3::ast::BV {
        let id = self.generate_id();
        let name = format!("{}_{}", name, id);
        z3::ast::BV::new_const(self.context, name, self.bits)
    }

    pub fn get_int_with_ctx<'a>(&self, context: &'a z3::Context, name: &str) -> z3::ast::BV<'a> {
        let id = self.generate_id();
        let name = format!("{}_{}", name, id);
        z3::ast::BV::new_const(context, name, self.bits)
    }

    pub fn get_const_int(&self, val: i64) -> z3::ast::BV {
        z3::ast::BV::from_i64(self.context, val, self.bits)
    }

    pub fn get_bool(&self, name: &str) -> z3::ast::Bool {
        let id = self.generate_id();
        let name = format!("{}_{}", name, id);
        z3::ast::Bool::new_const(self.context, name)
    }

    pub fn get_bool_with_ctx<'a>(&self, context: &'a z3::Context, name: &str) -> z3::ast::Bool<'a> {
        let id = self.generate_id();
        let name = format!("{}_{}", name, id);
        z3::ast::Bool::new_const(context, name)
    }

    pub fn get_const_bool(&self, val: bool) -> z3::ast::Bool {
        z3::ast::Bool::from_bool(self.context, val)
    }

    pub fn insert(&self, expr: &Bool) {
        if !self.is_finish {
            println!("{:?}", expr);
        }
        self.solver.assert(expr);
    }

    pub fn solve(&self) -> Option<z3::Model> {
        if self.solver.check() == SatResult::Sat {
            let model = self.solver.get_model().unwrap();
            return Some(model);
        }
        None

        // let xv = model.eval(&x, true).unwrap().as_i64().unwrap();
        // let yv = model.eval(&y, true).unwrap().as_i64().unwrap();
        // println!("x: {}", xv);
        // println!("y: {}", yv);
        // assert!(xv > yv);
        // assert!(yv % 7 == 2);
        // assert!(xv + 2 > 7);
    }
}
