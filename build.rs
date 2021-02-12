fn main() {
    let proto_root = "protos";
    println!("cargo:rerun-if-changed={}", proto_root);
    protoc_grpcio::compile_grpc_protos(
        &["protos/client/client.proto"],
        &[proto_root],
        "src/protos",
        None,
    )
    .expect("failed to compile grpc definitions");
}
