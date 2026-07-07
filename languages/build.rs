fn main() {
    std::env::set_var("PROTOC", protoc_bin_vendored::protoc_bin_path().expect("vendored protoc"));
    prost_build::Config::new()
        .compile_protos(&["proto/rhocalc_wire.proto"], &["proto/"])
        .expect("compile rhocalc_wire.proto");
}
