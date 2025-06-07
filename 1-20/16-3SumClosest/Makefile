Verifier = ./../../../verus/source/target-verus/release/verus

all:
	$(Verifier) ./main.rs --rlimit 30

compile:
	$(Verifier) --compile ./main.rs --rlimit 30

debug:
	$(Verifier) --expand-errors ./main.rs --rlimit 30

