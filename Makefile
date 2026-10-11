.DEFAULT_GOAL := all

OUT        := dist/bench2
MAC_ARM    := blocknet-faraday-bench2-arm64-macos
MAC_X86    := blocknet-faraday-bench2-amd64-macos
LINUX_X86  := blocknet-faraday-bench2-amd64-linux
WIN        := blocknet-faraday-bench2-amd64-windows.exe
LLVM_AR    := $$(command -v llvm-ar)

.PHONY: all clean
all:
	@mkdir -p $(OUT)
	cargo build --release --target aarch64-apple-darwin
	@cp target/aarch64-apple-darwin/release/sig-bench $(OUT)/$(MAC_ARM)
	cargo build --release --target x86_64-apple-darwin
	@cp target/x86_64-apple-darwin/release/sig-bench $(OUT)/$(MAC_X86)
	AR_x86_64_unknown_linux_gnu=$(LLVM_AR) cargo zigbuild --release --target x86_64-unknown-linux-gnu
	@cp target/x86_64-unknown-linux-gnu/release/sig-bench $(OUT)/$(LINUX_X86)
	AR_x86_64_pc_windows_gnu=$(LLVM_AR) cargo zigbuild --release --target x86_64-pc-windows-gnu
	@cp target/x86_64-pc-windows-gnu/release/sig-bench.exe $(OUT)/$(WIN)
	@echo ""
	@echo "4 binaries in $$(pwd)/$(OUT):"
	@ls -1sh $(OUT)

clean:
	cargo clean
	rm -rf $(OUT)
