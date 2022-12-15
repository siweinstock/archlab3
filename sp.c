#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>

#include "llsim.h"

#define sp_printf(a...)						\
	do {							\
		llsim_printf("sp: clock %d: ", llsim->clock);	\
		llsim_printf(a);				\
	} while (0)

int nr_simulated_instructions = 0;
FILE *inst_trace_fp = NULL, *cycle_trace_fp = NULL;

// branch prediction
int branch_counter = 0;     // simple 2-bit branch predictor
#define MIN(X, Y) (((X) < (Y)) ? (X) : (Y))
#define MAX(X, Y) (((X) > (Y)) ? (X) : (Y))

// HAZARD TYPES DEFINITION
#define NO_HAZARD 0
#define CTRL_HAZARD 1
#define DATA_HAZARD 2
#define REG_HAZARD 4
#define DATA_STALL 5

#define FETCH0  0
#define FETCH1  1
#define DEC0    2
#define DEC1    3
#define EXEC0   4
#define EXEC1   5


/*
 * DMA structure
 */
typedef struct dma_s {
    int src;            // source address
    int dst;            // destination address
    int len;            // total number of blocks to copy
    int state;          // DMA's FSM current state

    // control states
#define DMA_STATE_IDLE		0
#define DMA_STATE_FETCH		1
#define DMA_STATE_WAIT	    2
#define DMA_STATE_COPY	    3

} dma_t;

typedef struct sp_registers_s {
	// 6 32 bit registers (r[0], r[1] don't exist)
	int r[8];

	// 32 bit cycle counter
	int cycle_counter;

	// fetch0
	int fetch0_active; // 1 bit
	int fetch0_pc; // 16 bits

	// fetch1
	int fetch1_active; // 1 bit
	int fetch1_pc; // 16 bits

	// dec0
	int dec0_active; // 1 bit
	int dec0_pc; // 16 bits
	int dec0_inst; // 32 bits

	// dec1
	int dec1_active; // 1 bit
	int dec1_pc; // 16 bits
	int dec1_inst; // 32 bits
	int dec1_opcode; // 5 bits
	int dec1_src0; // 3 bits
	int dec1_src1; // 3 bits
	int dec1_dst; // 3 bits
	int dec1_immediate; // 32 bits

	// exec0
	int exec0_active; // 1 bit
	int exec0_pc; // 16 bits
	int exec0_inst; // 32 bits
	int exec0_opcode; // 5 bits
	int exec0_src0; // 3 bits
	int exec0_src1; // 3 bits
	int exec0_dst; // 3 bits
	int exec0_immediate; // 32 bits
	int exec0_alu0; // 32 bits
	int exec0_alu1; // 32 bits

	// exec1
	int exec1_active; // 1 bit
	int exec1_pc; // 16 bits
	int exec1_inst; // 32 bits
	int exec1_opcode; // 5 bits
	int exec1_src0; // 3 bits
	int exec1_src1; // 3 bits
	int exec1_dst; // 3 bits
	int exec1_immediate; // 32 bits
	int exec1_alu0; // 32 bits
	int exec1_alu1; // 32 bits
	int exec1_aluout;
} sp_registers_t;

/*
 * Master structure
 */
typedef struct sp_s {
	// local srams
#define SP_SRAM_HEIGHT	64 * 1024
	llsim_memory_t *srami, *sramd;

	unsigned int memory_image[SP_SRAM_HEIGHT];
	int memory_image_size;

	int start;

	sp_registers_t *spro, *sprn;

    // DMA
    dma_t* dma;

    // DMA control signals
    int dma_start;  // "kick" to trigger DMA activation
    int dma_busy;   // is DMA currently busy
    int mem_busy;   // is SRAM currently busy
} sp_t;

static void sp_reset(sp_t *sp)
{
	sp_registers_t *sprn = sp->sprn;

	memset(sprn, 0, sizeof(*sprn));
}

/*
 * opcodes
 */
#define ADD 0
#define SUB 1
#define LSF 2
#define RSF 3
#define AND 4
#define OR  5
#define XOR 6
#define LHI 7
#define LD 8
#define ST 9
#define CPY 10
#define POL 11
#define NOP 12
#define JLT 16
#define JLE 17
#define JEQ 18
#define JNE 19
#define JIN 20
#define HLT 24

static char opcode_name[32][4] = {"ADD", "SUB", "LSF", "RSF", "AND", "OR", "XOR", "LHI",
				 "LD", "ST", "U", "U", "U", "U", "U", "U",
				 "JLT", "JLE", "JEQ", "JNE", "JIN", "U", "U", "U",
				 "HLT", "U", "U", "U", "U", "U", "U", "U"};


// command classification macros
#define IS_ALU(opcode) ((opcode) == ADD || (opcode) == SUB || (opcode) == LSF || (opcode) == RSF || (opcode) == AND || (opcode) == OR || (opcode) == XOR || (opcode) == LHI)
#define IS_DMA(opcode) ((opcode) == CPY ||(opcode) == POL)
#define  IS_COND_BRANCH(opcode) ((opcode) == JLT || (opcode) == JLE || (opcode) == JEQ || (opcode) == JNE)
#define  IS_UNCOND_BRANCH(opcode) ((opcode) == JIN)
#define IS_BRANCH(opcode) (IS_COND_BRANCH((opcode)) || (opcode) == JIN)

// HAZARD CHECKING FUNCTIONS

int check_hazard_dec0(sp_t *sp) {
    sp_registers_t *spro = sp->spro;

    if (spro->dec1_active && spro->dec1_opcode == ST && ((spro->dec0_inst >> 25) & 0x1f) == LD) {
        return DATA_HAZARD;
    }
    return NO_HAZARD;
}

int check_hazard_dec1(sp_t *sp, int src) {
    sp_registers_t *spro = sp->spro;

    switch (src) {
        case 0:
            if (spro->exec0_active && spro->exec0_opcode == LD && spro->exec0_dst == spro->dec1_src0 && spro->dec1_src0 > 1) {
                return DATA_STALL;
            }

            if (spro->exec1_active && spro->dec1_src0 == 7 && (spro->exec1_opcode == JIN || IS_COND_BRANCH(spro->exec1_opcode) && spro->exec1_aluout)) {
                return CTRL_HAZARD;
            }
            else if (spro->exec1_active && spro->exec1_opcode == LD && spro->exec1_dst == spro->dec1_src0) {
                return DATA_HAZARD;
            }
            else if (spro->exec1_active && (IS_ALU(spro->exec1_opcode) || IS_DMA(spro->exec1_opcode)) && spro->exec1_dst == spro->dec1_src0) {
                return REG_HAZARD;
            }
            break;
        case 1:
            if (spro->exec0_active && spro->exec0_opcode == LD && spro->exec0_dst == spro->dec1_src1 && spro->dec1_src1 > 1) {
                return DATA_STALL;
            }

            if (spro->exec1_active && spro->dec1_src1 == 7 && (spro->exec1_opcode == JIN || IS_COND_BRANCH(spro->exec1_opcode) && spro->exec1_aluout)) {
                return CTRL_HAZARD;
            }
            else if (spro->exec1_active && spro->exec1_opcode == LD && spro->exec1_dst == spro->dec1_src1) {
                return DATA_HAZARD;
            }
            else if (spro->exec1_active && (IS_ALU(spro->exec1_opcode) || IS_DMA(spro->exec1_opcode)) && spro->exec1_dst == spro->dec1_src1) {
                return REG_HAZARD;
            }
            break;
        default:
            // unreachable
            break;
    }
    return NO_HAZARD;
}

// TODO
int check_hazard_exec0(sp_t *sp, int src) {
    sp_registers_t *spro = sp->spro;

    switch (src) {
        case 0:
            if (spro->exec1_active && spro->exec0_src0 == 7 && ((IS_COND_BRANCH(spro->exec1_opcode) && spro->exec1_aluout) ||
                    IS_UNCOND_BRANCH(spro->exec1_opcode)) && spro->exec0_src0 > 1) {
                return CTRL_HAZARD;
            }
            else if (spro->exec1_active && (IS_ALU(spro->exec1_opcode) || IS_DMA(spro->exec1_opcode)) &&
                    spro->exec1_dst == spro->exec0_src0  && spro->exec0_src0 > 1) {
                return REG_HAZARD;
            }
            break;
        case 1:
            if (spro->exec1_active && spro->exec0_src1 == 7 && ((IS_COND_BRANCH(spro->exec1_opcode) && spro->exec1_aluout) ||
                    IS_UNCOND_BRANCH(spro->exec1_opcode)) && spro->exec0_src1 > 1) {
                return CTRL_HAZARD;
            }
            else if (spro->exec1_active && (IS_ALU(spro->exec1_opcode) || IS_DMA(spro->exec1_opcode)) &&
                     spro->exec1_dst == spro->exec0_src1  && spro->exec0_src1 > 1) {
                return REG_HAZARD;
            }
            break;
        default:
            // unreachable
            break;
    }
    return  NO_HAZARD;
}

// stall pipeline
void stall(sp_t *sp, int stage) {
    sp_registers_t *spro = sp->spro;
    sp_registers_t *sprn = sp->sprn;

    switch (stage) {
        case DEC1:
            sprn->exec1_active = 0;

            sprn->exec0_active = 1;
            sprn->exec0_pc = 0;
            sprn->exec0_inst = 0;
            sprn->exec0_opcode = NOP;
            sprn->exec0_dst = 0;
            sprn->exec0_src0 = 0;
            sprn->exec0_src1 = 0;
            sprn->exec0_immediate = 0;

            sprn->fetch0_active = spro->fetch0_active;
            sprn->fetch0_pc = spro->fetch0_pc;

            sprn->fetch1_active = spro->fetch1_active;
            sprn->fetch1_pc = spro->fetch1_pc;

            sprn->dec0_active = spro->dec0_active;
            sprn->dec0_pc = spro->dec0_pc;
            sprn->dec0_inst = spro->dec0_inst;

            sprn->dec1_active = spro->dec1_active;
            sprn->dec1_pc = spro->dec1_pc;
            sprn->dec1_inst = spro->dec1_inst;
            sprn->dec1_opcode = spro->dec1_opcode;
            sprn->dec1_dst = spro->dec1_dst;
            sprn->dec1_src0 = spro->dec1_src0;
            sprn->dec1_src1 = spro->dec1_src1;
            sprn->dec1_immediate = spro->dec1_immediate;
            break;

        case DEC0:
            sprn->fetch0_active = spro->fetch1_active;
            sprn->fetch0_pc = spro->fetch1_pc;

            sprn->fetch1_active = 0;

            sprn->dec0_active = spro->dec0_active;
            sprn->dec0_pc = spro->dec0_pc;
            sprn->dec0_inst = spro->dec0_inst;

            sprn->dec1_active = 0;
            break;

        default:
            break;
    }

}

// flush pipeline and load correct instruction
void flush(sp_t *sp, int stage, int pc) {
    sp_registers_t *sprn = sp->sprn;
    sp_registers_t *spro = sp->spro;

    switch (stage) {
        case DEC0:
            sprn->fetch0_active = 1;
            sprn->fetch0_pc = pc;
            sprn->fetch1_active = 0;
            sprn->dec0_active = 0;
            break;

        case EXEC1:
            sprn->exec1_active = 0;
            sprn->exec0_active = 0;
            sprn->dec1_active = 0;
            sprn->dec0_active = 0;
            sprn->fetch1_active = 0;
            sprn->fetch0_active = 1;
            sprn->fetch0_pc = pc;
            break;

        default:
            break;

    }

}

// branch predictor
void predict_branch(sp_t *sp) {
    sp_registers_t *spro = sp->spro;
    sp_registers_t *sprn = sp->sprn;

    int pc;

    if (IS_COND_BRANCH(spro->exec1_opcode)) {
        if (spro->exec1_aluout)
            sprn->r[7] = spro->exec1_pc;

        // update pc and branch counter: (taken ? Yes : No);
        // MIN and MAX to prevent a 2-bit overflow
        pc = spro->exec1_aluout ? (spro->exec1_immediate & 0xffff) : spro->exec1_pc + 1;
        branch_counter = spro->exec1_aluout ? MAX(3, branch_counter+1) : MIN(0, branch_counter-1);
    }
    // JIN
    else {
        sprn->r[7] = spro->exec1_pc;
        pc = spro->exec1_alu0 & 0xffff;
    }

    if ((spro->fetch0_active && (spro->fetch0_pc != pc)) ||
        (spro->fetch1_active && (spro->fetch1_pc != pc)) ||
        (spro->dec0_active && (spro->dec0_pc != pc)) ||
        (spro->dec1_active && (spro->dec1_pc != pc)) ||
        (spro->exec0_active && (spro->exec0_pc != pc))) {
        flush(sp, EXEC1, pc);
    }

}


static void dump_sram(sp_t *sp, char *name, llsim_memory_t *sram)
{
	FILE *fp;
	int i;

	fp = fopen(name, "w");
	if (fp == NULL) {
                printf("couldn't open file %s\n", name);
                exit(1);
	}
	for (i = 0; i < SP_SRAM_HEIGHT; i++)
		fprintf(fp, "%08x\n", llsim_mem_extract(sram, i, 31, 0));
	fclose(fp);
}

static void sp_ctl(sp_t *sp)
{
	sp_registers_t *spro = sp->spro;
	sp_registers_t *sprn = sp->sprn;
	int i;

	fprintf(cycle_trace_fp, "cycle %d\n", spro->cycle_counter);
	fprintf(cycle_trace_fp, "cycle_counter %08x\n", spro->cycle_counter);
	for (i = 2; i <= 7; i++)
		fprintf(cycle_trace_fp, "r%d %08x\n", i, spro->r[i]);

	fprintf(cycle_trace_fp, "fetch0_active %08x\n", spro->fetch0_active);
	fprintf(cycle_trace_fp, "fetch0_pc %08x\n", spro->fetch0_pc);

	fprintf(cycle_trace_fp, "fetch1_active %08x\n", spro->fetch1_active);
	fprintf(cycle_trace_fp, "fetch1_pc %08x\n", spro->fetch1_pc);

	fprintf(cycle_trace_fp, "dec0_active %08x\n", spro->dec0_active);
	fprintf(cycle_trace_fp, "dec0_pc %08x\n", spro->dec0_pc);
	fprintf(cycle_trace_fp, "dec0_inst %08x\n", spro->dec0_inst); // 32 bits

	fprintf(cycle_trace_fp, "dec1_active %08x\n", spro->dec1_active);
	fprintf(cycle_trace_fp, "dec1_pc %08x\n", spro->dec1_pc); // 16 bits
	fprintf(cycle_trace_fp, "dec1_inst %08x\n", spro->dec1_inst); // 32 bits
	fprintf(cycle_trace_fp, "dec1_opcode %08x\n", spro->dec1_opcode); // 5 bits
	fprintf(cycle_trace_fp, "dec1_src0 %08x\n", spro->dec1_src0); // 3 bits
	fprintf(cycle_trace_fp, "dec1_src1 %08x\n", spro->dec1_src1); // 3 bits
	fprintf(cycle_trace_fp, "dec1_dst %08x\n", spro->dec1_dst); // 3 bits
	fprintf(cycle_trace_fp, "dec1_immediate %08x\n", spro->dec1_immediate); // 32 bits

	fprintf(cycle_trace_fp, "exec0_active %08x\n", spro->exec0_active);
	fprintf(cycle_trace_fp, "exec0_pc %08x\n", spro->exec0_pc); // 16 bits
	fprintf(cycle_trace_fp, "exec0_inst %08x\n", spro->exec0_inst); // 32 bits
	fprintf(cycle_trace_fp, "exec0_opcode %08x\n", spro->exec0_opcode); // 5 bits
	fprintf(cycle_trace_fp, "exec0_src0 %08x\n", spro->exec0_src0); // 3 bits
	fprintf(cycle_trace_fp, "exec0_src1 %08x\n", spro->exec0_src1); // 3 bits
	fprintf(cycle_trace_fp, "exec0_dst %08x\n", spro->exec0_dst); // 3 bits
	fprintf(cycle_trace_fp, "exec0_immediate %08x\n", spro->exec0_immediate); // 32 bits
	fprintf(cycle_trace_fp, "exec0_alu0 %08x\n", spro->exec0_alu0); // 32 bits
	fprintf(cycle_trace_fp, "exec0_alu1 %08x\n", spro->exec0_alu1); // 32 bits

	fprintf(cycle_trace_fp, "exec1_active %08x\n", spro->exec1_active);
	fprintf(cycle_trace_fp, "exec1_pc %08x\n", spro->exec1_pc); // 16 bits
	fprintf(cycle_trace_fp, "exec1_inst %08x\n", spro->exec1_inst); // 32 bits
	fprintf(cycle_trace_fp, "exec1_opcode %08x\n", spro->exec1_opcode); // 5 bits
	fprintf(cycle_trace_fp, "exec1_src0 %08x\n", spro->exec1_src0); // 3 bits
	fprintf(cycle_trace_fp, "exec1_src1 %08x\n", spro->exec1_src1); // 3 bits
	fprintf(cycle_trace_fp, "exec1_dst %08x\n", spro->exec1_dst); // 3 bits
	fprintf(cycle_trace_fp, "exec1_immediate %08x\n", spro->exec1_immediate); // 32 bits
	fprintf(cycle_trace_fp, "exec1_alu0 %08x\n", spro->exec1_alu0); // 32 bits
	fprintf(cycle_trace_fp, "exec1_alu1 %08x\n", spro->exec1_alu1); // 32 bits
	fprintf(cycle_trace_fp, "exec1_aluout %08x\n", spro->exec1_aluout);

	fprintf(cycle_trace_fp, "\n");

	sp_printf("cycle_counter %08x\n", spro->cycle_counter);
	sp_printf("r2 %08x, r3 %08x\n", spro->r[2], spro->r[3]);
	sp_printf("r4 %08x, r5 %08x, r6 %08x, r7 %08x\n", spro->r[4], spro->r[5], spro->r[6], spro->r[7]);
	sp_printf("fetch0_active %d, fetch1_active %d, dec0_active %d, dec1_active %d, exec0_active %d, exec1_active %d\n",
		  spro->fetch0_active, spro->fetch1_active, spro->dec0_active, spro->dec1_active, spro->exec0_active, spro->exec1_active);
	sp_printf("fetch0_pc %d, fetch1_pc %d, dec0_pc %d, dec1_pc %d, exec0_pc %d, exec1_pc %d\n",
		  spro->fetch0_pc, spro->fetch1_pc, spro->dec0_pc, spro->dec1_pc, spro->exec0_pc, spro->exec1_pc);

	sprn->cycle_counter = spro->cycle_counter + 1;

	if (sp->start)
		sprn->fetch0_active = 1;

    // fetch0
	sprn->fetch1_active = 0;
    if (spro->fetch0_active) {
        llsim_mem_read(sp->srami, spro->fetch0_pc);    // read instruction @ pc
        sprn->fetch0_pc = (spro->fetch0_pc + 1) & 0xffff;           // advance PC (and handle overflow)

        sprn->fetch1_active = 1;
        sprn->fetch1_pc = spro->fetch0_pc;
	}
    else {
        sprn->fetch1_active = 0;    // propagate inactivity
    }

	// fetch1
    if (spro->fetch1_active) {
        sprn->dec0_inst = llsim_mem_extract(sp->srami, spro->fetch1_pc, 31, 0);

        sprn->dec0_active = 1;
        sprn->dec0_pc = spro->fetch1_pc;
    }
    else {
        sprn->dec0_active = 0;    // propagate inactivity;
    }
	
	// dec0
    if (spro->dec0_active) {
        // branch prediction is 'taken'
        if (IS_COND_BRANCH((spro->dec0_inst >> 25) & 0x1f) && branch_counter > 1) {
            flush(sp, DEC0, (spro->dec0_inst & 0xffff));
        }

        // check for RAW hazard
        switch (check_hazard_dec0(sp)) {
            // if RAW then stall command
            case DATA_HAZARD:
                stall(sp, DEC0);
                break;

            // if no hazard continue as usual
            default:
                // parse operation
                sprn->dec1_opcode = (spro->dec0_inst >> 25) & 0x1f;
                sprn->dec1_dst = (spro->dec0_inst >> 22) & 0x7;
                sprn->dec1_src0 = (spro->dec0_inst >> 19) & 0x7;
                sprn->dec1_src1 = (spro->dec0_inst >> 16) & 0x7;
                sprn->dec1_immediate = spro->dec0_inst & 0xffff;

                // sign extend immediate
                sprn->dec1_immediate += (int)((sprn->dec1_immediate & 0x8000) ? 0xffff0000 : 0x0);

                sprn->dec1_inst = spro->dec0_inst;
                sprn->dec1_active = 1;
                sprn->dec1_pc = spro->dec0_pc;
                break;
        }
    }
    else {
        sprn->dec1_active = 0;
    }

	// dec1
    if (spro->dec1_active) {

        // check for RAW and stall if necessary
        if (check_hazard_dec1(sp, 0) == DATA_STALL || check_hazard_dec1(sp, 1) == DATA_STALL) {
            stall(sp, DEC1);
        }
        // check for hazards that can be solved using bypasses
        else {
            switch (spro->dec1_src0) {
                case 0:
                    sprn->exec0_alu0 = 0;
                    break;
                case 1:
                    sprn->r[1] = spro->dec1_immediate;
                    sprn->exec0_alu0 = spro->dec1_immediate;
                    break;
                    // [2..7]
                default:
                    switch (check_hazard_dec1(sp, 0)) {
                        case NO_HAZARD:
                            sprn->exec0_alu0 = spro->r[spro->dec1_src0];
                            break;
                        case CTRL_HAZARD:
                            sprn->exec0_alu0 = spro->exec1_pc;
                            break;
                        case DATA_HAZARD:
                            sprn->exec0_alu0 = llsim_mem_extract_dataout(sp->sramd, 31, 0);
                            break;
                        case REG_HAZARD:
                            sprn->exec0_alu0 = spro->exec1_aluout;
                            break;
                    }
                    break;
            }

            switch (spro->dec1_src1) {
                case 0:
                    sprn->exec0_alu1 = 0;
                    break;
                case 1:
                    sprn->r[1] = spro->dec1_immediate;
                    sprn->exec0_alu1 = spro->dec1_immediate;
                    break;
                    // [2..7]
                default:
                    switch (check_hazard_dec1(sp, 1)) {
                        case NO_HAZARD:
                            sprn->exec0_alu1 = spro->r[spro->dec1_src1];
                            break;
                        case CTRL_HAZARD:
                            sprn->exec0_alu1 = spro->exec1_pc;
                            break;
                        case DATA_HAZARD:
                            sprn->exec0_alu1 = llsim_mem_extract_dataout(sp->sramd, 31, 0);
                            break;
                        case REG_HAZARD:
                            sprn->exec0_alu1 = spro->exec1_aluout;
                            break;
                    }
                    break;
            }
        }

        sprn->exec0_pc = spro->dec1_pc;
        sprn->exec0_inst = spro->dec1_inst;
        sprn->exec0_opcode = spro->dec1_opcode;
        sprn->exec0_dst = spro->dec1_dst;
        sprn->exec0_src0 = spro->dec1_src0;
        sprn->exec0_src1 = spro->dec1_src1;
        sprn->exec0_immediate = spro->dec1_immediate;
        sprn->exec0_active = 1;
    }
    else {
        sprn->exec0_active = 0;
    }

	// exec0
    if (spro->exec0_active) {
        int alu0 = spro->exec0_alu0, alu1 = spro->exec0_alu1;

        // if stall, then preserve state
        if (spro->exec0_opcode == NOP) {
            sprn->exec1_pc = spro->exec1_pc;
            sprn->exec1_inst = spro->exec1_inst;
            sprn->exec1_opcode = spro->exec1_opcode;
            sprn->exec1_dst = spro->exec1_dst;
            sprn->exec1_src0 = spro->exec1_src0;
            sprn->exec1_src1 = spro->exec1_src1;
            sprn->exec1_immediate = spro->exec1_immediate;

            sprn->exec1_alu0 = spro->exec1_alu0;
            sprn->exec1_alu1 = spro->exec1_alu1;

            sprn->exec1_active = 0;
        }
        // if not in a stall resume operation
        else {
            switch (spro->exec0_src0) {
                case 0:
                case 1:
                    break;
                    // src in [2..7]
                default:
                    switch (check_hazard_exec0(sp, 0)) {
                        case CTRL_HAZARD:
                            alu0 = spro->exec1_pc;
                            break;
                        case REG_HAZARD:
                            alu0 = spro->exec1_aluout;
                            break;
                    }
                    break;
            }

            switch (spro->exec0_src1) {
                case 0:
                case 1:
                    break;
                    // src in [2..7]
                default:
                    switch (check_hazard_exec0(sp, 1)) {
                        case CTRL_HAZARD:
                            alu1 = spro->exec1_pc;
                            break;
                        case REG_HAZARD:
                            alu1 = spro->exec1_aluout;
                            break;
                    }
                    break;
            }

            switch (spro->exec0_opcode) {
                case ADD:
                    sprn->exec1_aluout = alu0 + alu1;
                    break;
                case SUB:
                    sprn->exec1_aluout = alu0 - alu1;
                    break;
                case LSF:
                    sprn->exec1_aluout = alu0 << alu1;
                    break;
                case RSF:
                    sprn->exec1_aluout = alu0 >> alu1;
                    break;
                case AND:
                    sprn->exec1_aluout = alu0 & alu1;
                    break;
                case OR:
                    sprn->exec1_aluout = alu0 | alu1;
                    break;
                case XOR:
                    sprn->exec1_aluout = alu0 ^ alu1;
                    break;
                case LHI:
                    sprn->exec1_aluout = (alu0 & 0xffff) | (alu1 << 16);
                    break;
                case LD:
                    llsim_mem_read(sp->sramd, alu1);
                    break;
                case ST:
                    break;
                case JLT:
                    sprn->exec1_aluout = (alu0 < alu1) ? 1 : 0;
                    break;
                case JLE:
                    sprn->exec1_aluout = (alu0 <= alu1) ? 1 : 0;
                    break;
                case JEQ:
                    sprn->exec1_aluout = (alu0 == alu1) ? 1 : 0;
                    break;
                case JNE:
                    sprn->exec1_aluout = (alu0 != alu1) ? 1 : 0;
                    break;
                case JIN:
                    sprn->exec1_aluout = 1;
                    break;
                case HLT:
                    break;

            }

            sprn->exec1_pc = spro->exec0_pc;
            sprn->exec1_inst = spro->exec0_inst;
            sprn->exec1_opcode = spro->exec0_opcode;
            sprn->exec1_dst = spro->exec0_dst;
            sprn->exec1_src0 = spro->exec0_src0;
            sprn->exec1_src1 = spro->exec0_src1;
            sprn->exec1_immediate = spro->exec0_immediate;

            sprn->exec1_alu0 = alu0;
            sprn->exec1_alu1 = alu1;

            sprn->exec1_active = 1;
        }
    }
    else {
        sprn->exec1_active = 0;
    }

	// exec1
	if (spro->exec1_active) {
        if (spro->exec1_opcode == HLT) {
			llsim_stop();
			dump_sram(sp, "srami_out.txt", sp->srami);
			dump_sram(sp, "sramd_out.txt", sp->sramd);
		}
        else {
            switch (spro->exec1_opcode) {
                case ADD:
                case SUB:
                case LSF:
                case RSF:
                case AND:
                case OR:
                case XOR:
                case LHI:
                    if (spro->exec1_dst > 1)
                        sprn->r[spro->exec1_dst] = spro->exec1_aluout;
                    break;
                case LD:
                    if (spro->exec1_dst > 1)
                        sprn->r[spro->exec1_dst] =  llsim_mem_extract(sp->sramd, spro->exec1_alu1, 31, 0);
                    break;
                case ST:
                    llsim_mem_set_datain(sp->sramd, spro->exec1_alu0, 31, 0);
                    llsim_mem_write(sp->sramd, spro->exec1_alu1);
                    break;
                case JLT:
                case JLE:
                case JEQ:
                case JNE:
                case JIN:
                    predict_branch(sp);
                    break;
                // HLT already taken care of in provided code
            }
	    }
    }
}

static void sp_run(llsim_unit_t *unit)
{
	sp_t *sp = (sp_t *) unit->private;
	//	sp_registers_t *spro = sp->spro;
	//	sp_registers_t *sprn = sp->sprn;

	//	llsim_printf("-------------------------\n");

	if (llsim->reset) {
		sp_reset(sp);
		return;
	}

	sp->srami->read = 0;
	sp->srami->write = 0;
	sp->sramd->read = 0;
	sp->sramd->write = 0;

	sp_ctl(sp);
}

static void sp_generate_sram_memory_image(sp_t *sp, char *program_name)
{
        FILE *fp;
        int addr, i;

        fp = fopen(program_name, "r");
        if (fp == NULL) {
                printf("couldn't open file %s\n", program_name);
                exit(1);
        }
        addr = 0;
        while (addr < SP_SRAM_HEIGHT) {
                fscanf(fp, "%08x\n", &sp->memory_image[addr]);
                //              printf("addr %x: %08x\n", addr, sp->memory_image[addr]);
                addr++;
                if (feof(fp))
                        break;
        }
	sp->memory_image_size = addr;

        fprintf(inst_trace_fp, "program %s loaded, %d lines\n", program_name, addr);

	for (i = 0; i < sp->memory_image_size; i++) {
		llsim_mem_inject(sp->srami, i, sp->memory_image[i], 31, 0);
		llsim_mem_inject(sp->sramd, i, sp->memory_image[i], 31, 0);
	}
}

void sp_init(char *program_name)
{
	llsim_unit_t *llsim_sp_unit;
	llsim_unit_registers_t *llsim_ur;
	sp_t *sp;

	llsim_printf("initializing sp unit\n");

	inst_trace_fp = fopen("inst_trace.txt", "w");
	if (inst_trace_fp == NULL) {
		printf("couldn't open file inst_trace.txt\n");
		exit(1);
	}

	cycle_trace_fp = fopen("cycle_trace.txt", "w");
	if (cycle_trace_fp == NULL) {
		printf("couldn't open file cycle_trace.txt\n");
		exit(1);
	}

	llsim_sp_unit = llsim_register_unit("sp", sp_run);
	llsim_ur = llsim_allocate_registers(llsim_sp_unit, "sp_registers", sizeof(sp_registers_t));
	sp = llsim_malloc(sizeof(sp_t));
	llsim_sp_unit->private = sp;
	sp->spro = llsim_ur->old;
	sp->sprn = llsim_ur->new;

	sp->srami = llsim_allocate_memory(llsim_sp_unit, "srami", 32, SP_SRAM_HEIGHT, 0);
	sp->sramd = llsim_allocate_memory(llsim_sp_unit, "sramd", 32, SP_SRAM_HEIGHT, 0);
	sp_generate_sram_memory_image(sp, program_name);

	sp->start = 1;
	
	// c2v_translate_end
}
