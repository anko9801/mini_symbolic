use std::ops::Add;
use z3::*;
use z3::{
    ast,
    ast::{Array, Ast, AstKind, Bool, Dynamic, Float, Int, Real, BV},
};

// let project = project::Project::new(&ctx, 64);
// let x = project.get_int("x");
// let y = project.get_int("y");
// let zero = project.get_const_int(0);
// project.insert(&x._eq(&y));
// project.insert(&x._eq(&zero));
// assert_eq!(project.solver.check(), z3::SatResult::Sat);
// let model = project.solver.get_model().unwrap();
// let x_val = model.eval(&x, true).unwrap().as_i64().unwrap();
// let y_val = model.eval(&y, true).unwrap().as_i64().unwrap();
// println!("x: {} y: {}", x_val, y_val);
// assert_eq!(x_val, 0);
// assert_eq!(y_val, 0);
pub fn test() {
    let _ = env_logger::try_init();
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    let x = ast::Int::new_const(&ctx, "x");
    let y = ast::Int::new_const(&ctx, "y");

    let zero = ast::Int::from_i64(&ctx, 0);
    let two = ast::Int::from_i64(&ctx, 2);
    let seven = ast::Int::from_i64(&ctx, 7);

    // x > y
    solver.assert(&x.gt(&y));
    // y > 0
    solver.assert(&y.gt(&zero));
    // y % 7 == 2
    solver.assert(&y.rem(&seven)._eq(&two));
    // x + 2 > 7
    solver.assert(&ast::Int::add(&ctx, &[&x, &two]).gt(&seven));

    assert_eq!(solver.check(), SatResult::Sat);

    let model = solver.get_model().unwrap();

    let xv = model.eval(&x, true).unwrap().as_i64().unwrap();
    let yv = model.eval(&y, true).unwrap().as_i64().unwrap();
    println!("x: {}", xv);
    println!("y: {}", yv);
    assert!(xv > yv);
    assert!(yv % 7 == 2);
    assert!(xv + 2 > 7);
}

pub fn tomori_test() {
    let _ = env_logger::try_init();
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let rax = ast::BV::new_const(&ctx, "rax", 64);
    let rdx = ast::BV::new_const(&ctx, "rdx", 64);
    let rsi = ast::BV::new_const(&ctx, "rsi", 64);

    let c2 = ast::BV::from_i64(&ctx, 2, 64);
    let c3 = ast::BV::from_i64(&ctx, 3, 64);
    let c16 = ast::BV::from_i64(&ctx, 16, 64);

    let solver = Solver::new(&ctx);
    solver.assert(&rsi._eq(&c2));
    solver.assert(&rax._eq(&c16));
    // solver.assert(&rdx._eq(&c2));
    solver.assert(&rsi.bvmul(&rdx)._eq(&rax));
    assert_eq!(solver.check(), SatResult::Sat);

    let model = solver.get_model().unwrap();
    let raxv = model.eval(&rax, true).unwrap().as_i64().unwrap();
    let rdxv = model.eval(&rdx, true).unwrap().as_i64().unwrap();
    let rsiv = model.eval(&rsi, true).unwrap().as_i64().unwrap();
    println!("rax: {}", raxv);
    println!("rdx: {}", rdxv);
    println!("rsi: {}", rsiv);
}

pub fn arch_test() {
    let _ = env_logger::try_init();
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let src = ast::Int::new_const(&ctx, "src1");
    let dst = ast::Int::new_const(&ctx, "dst1");
    let res = ast::Int::new_const(&ctx, "res1");

    let solver = Solver::new(&ctx);
    solver.assert(&src.add(&dst)._eq(&res));

    let ZF = ast::Bool::new_const(&ctx, "ZF");
    let SF = ast::Bool::new_const(&ctx, "SF");
    let OF = ast::Bool::new_const(&ctx, "OF");
    let zero = ast::Int::from_i64(&ctx, 0);
    solver.assert(&res._eq(&zero)._eq(&ZF));
    // self.store_flag_symvar("ZF", ZF)
    // SF = Bool("bool_%x_add_SF" % _id)
    // OF = Bool("bool_%x_add_OF" % _id)
    // self.solver.add([SF == (res < 0), OF == False]) # FIXME: OF
    // self.store_flag_symvar("SF", SF)
    // self.store_flag_symvar("OF", OF)
}
