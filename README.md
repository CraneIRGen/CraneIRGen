# CraneIRGen

CraneIRGen: A Differential Testing Framework for the Cranelift Compiler


## Getting Started
The architecture-aware profiles mentioned in the paper refer to the toml files in the configs directory. CraneIRGen has two modes: the `single` mode corresponds to the `Target-Specific` test mentioned in the paper, and the `intersection` mode is designed to generate compatible IR files, which can be used for `differential testing`.


1. Set environments.

CraneIRGen should run well on a server with Ubuntu 22.04.
Please download [Docker](https://docs.docker.com/get-docker/) first.
```bash
sudo docker build -t craneirgen .
sudo docker run -it craneirgen # run a docker container
```

2. Start generating cranelift ir files

```bash
# in the docker container 
cd home/ubuntu/CraneIRGen/
cargo run --bin ir_generator
# single mode example
cargo run --bin ir_generator -- --num 1000 single configs/arch_x86.toml output
# intersection mode example 
cargo run --bin ir_generator -- --num 1000 intersection configs/arch_x86.toml configs/arch_aarch64.toml configs/arch_riscv64.toml configs/arch_s390x.toml output
```

The generated IR files are stored in `home/ubuntu/CraneIRGen/output`.

