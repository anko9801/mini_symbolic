use ouroboros::self_referencing;
use z3::ast::Ast;

#[self_referencing]
struct Project {
    cfg: z3::Config,
    ctx: z3::Context,
    #[borrows(ctx)]
    #[covariant]
    solver: z3::Solver<'this>,
    id: u32,
}
impl Project {
    fn _new() -> Self {
        let cfg = z3::Config::new();
        let ctx = z3::Context::new(&cfg);
        ProjectBuilder {
            cfg,
            ctx,
            solver_builder: |ctx: &z3::Context| z3::Solver::new(ctx),
            id: 0,
        }.build()
    }

    fn add_int_const(&self, name: &str) {
        let x = z3::ast::Int::new_const(self.borrow_ctx(), name);
        let y = x.clone();
        let zero = z3::ast::Int::from_i64(self.borrow_ctx(), 0);

        self.borrow_solver().assert(&x._eq(&zero));
        assert_eq!(self.borrow_solver().check(), z3::SatResult::Sat);

        let model = self.borrow_solver().get_model().unwrap();
        let x_val = model.eval(&x, true).unwrap().as_i64().unwrap();
        let y_val = model.eval(&y, true).unwrap().as_i64().unwrap();
        println!("x: {} y: {}", x_val, y_val);
        let y_val = model.eval(&y, true).unwrap().as_i64().unwrap();
        println!("x: {} y: {}", x_val, y_val);
        assert_eq!(x_val, 0);
        assert_eq!(y_val, 0);
    }
    fn generate_id(&mut self) -> u32 {
        self.with_id_mut(|id| {
            *id += 1;
            *id
        })
    }
    pub fn get_const_int(&mut self, name: &str) -> z3::ast::Int {
        let id = self.generate_id();
        let name = format!("{}_{}", name, id);
        z3::ast::Int::new_const(self.borrow_ctx(), name)
    }
    pub fn get_const_int_static_id(&self, name: &str, id: u32) -> z3::ast::Int {
        let name = format!("{}_{}", name, id);
        z3::ast::Int::new_const(self.borrow_ctx(), name)
    }
}

fn main() {
    let mut project = Project::_new();
    let idx = project.generate_id();
    let idy = project.generate_id();
    let x = project.get_const_int_static_id("x", idx);
    let y = project.get_const_int_static_id("y", idy);
    project.borrow_solver().assert(&x.gt(&y));
    assert_eq!(project.borrow_solver().check(), z3::SatResult::Sat);
}
