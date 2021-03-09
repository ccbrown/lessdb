fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=../protos/client/client.proto");
    protoc_grpcio::compile_grpc_protos(
        &["../protos/client/client.proto"],
        &["../protos"],
        "src/protos",
        None,
    )
    .expect("failed to compile grpc definitions");
}
