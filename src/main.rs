mod arch;
mod parse;
mod project;
mod test;

fn main() {
    let mut cfg = z3::Config::new();
    cfg.set_model_generation(true);
    let ctx = z3::Context::new(&cfg);
    let mut code = parse::Code::new(&ctx);
    code.solve();
}
