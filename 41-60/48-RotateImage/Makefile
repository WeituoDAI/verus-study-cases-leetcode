Verifier = ./../../../verus/source/target-verus/release/verus

all:
	$(Verifier) --no-erasure-check --rlimit=40 ./main.rs

compile:
	$(Verifier) --compile ./main.rs

debug:
	$(Verifier) --no-erasure-check --expand-errors ./main.rs

