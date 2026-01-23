fn main() {
    // Compile LALRPOP grammars from src/generated/ subdirectory
    lalrpop::Configuration::new()
        .set_in_dir("src/generated")
        .process()
        .unwrap();
}
