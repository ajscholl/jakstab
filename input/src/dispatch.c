
enum op_t {ADD = 0, SUB = 1, MUL = 2};

int __attribute__((regparm(2))) dispatch(enum op_t op, int a, int b) {
	static void *tbl[] = {&&handleAdd, &&handleSub, &&handleMul};
	goto *tbl[op];
handleAdd:
	return a + b;
handleSub:
	return a - b;
handleMul:
	return a * b;
}

#define NOP __asm("nop;");
#define NOP4 NOP NOP NOP NOP;

int start(void) {
    // compute ((2 + 3) * 4) - 5
    int n1, n2, n3;
    n1 = dispatch(ADD, 2, 3);
    NOP4 NOP4 NOP4 NOP
    n2 = dispatch(MUL, n1, 4);
    NOP4 NOP4 NOP4 NOP
    n3 = dispatch(SUB, n2, 5);
    return n3;
}

