fn main() {
    let program = bril_rs::load_program();

    println!("{}", serde_json::to_string_pretty(&program).unwrap());
}
