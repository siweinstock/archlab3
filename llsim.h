#ifndef _LLSIM_H_
#define _LLSIM_H_
typedef long long i64;

void sp_init(char *program_name);

/*
 * support functions
 */
#define llsim_assert(cond, args...)					\
	do {								\
		if (!(cond)) {						\
			printf("llsim: clock %d: assertion failed at file %s line %d: ", llsim->clock, __FILE__, __LINE__); \
			printf(args);					\
			exit (1);					\
		}							\
	} while (0);							\

#define llsim_printf	printf

#define llsim_error(args...) llsim_assert(0, args)

static inline int bitmask0(bits)
{
	if (bits == 32)
		return -1;
	else
		return ((((int) 1) << bits) - 1);
}

static inline int bitmask(int msb, int lsb)
{
	return bitmask0(msb - lsb + 1) << lsb;
}

static inline int sbs(int val, int msb, int lsb)
{
	if (msb == 31 && lsb == 0)
		return val;
	else
		return ((val >> lsb) & bitmask0(msb - lsb + 1));
}

static inline int sb(int val, int bit)
{
	return (val >> bit) & 1;
}

static inline int ssbs(int val, int msb, int lsb)
{
	int val2;

	val2 = sbs(val, msb, lsb);
	if (sb(val2,msb))
		val2 -= (1 << (msb+1));
	return val2;
}

static inline int rbs(int val, int data, int msb, int lsb)
{
	val = (val & (~bitmask(msb,lsb))) | ((data << lsb) & bitmask(msb,lsb));
	return val;
}

static inline i64 lbitmask0(int bits)
{
	if (bits == 64)
		return -1;
	else
		return ((((i64) 1) << bits) - 1);
}

static inline i64 lbitmask(int msb, int lsb)
{
	return lbitmask0(msb - lsb + 1) << lsb;
}

static inline i64 lsbs(i64 val, int msb, int lsb)
{
	if (msb == 63 && lsb == 0)
		return val;
	else
		return ((val >> lsb) & lbitmask0(msb - lsb + 1));
}

static inline i64 lrbs(i64 val, int data, int msb, int lsb)
{
	val = (val & (~lbitmask(msb,lsb))) | ((data << lsb) & bitmask(msb,lsb));
	return val;
}

static inline int cbs(int val, int msb, int lsb)
{
        return (val << lsb) & bitmask(msb,lsb);
}

static inline int csbs(int val, int msb, int lsb, int newmsb, int newlsb)
{
	return cbs(sbs(val,msb,lsb),newmsb,newlsb);
}


static inline int cb(int val, int pos)
{
	return cbs(val,pos,pos);
}

/*
 * simulated unit registers
 */
typedef struct llsim_unit_registers_s {
	char *name;
	int size;
	void *old,*new;
	struct llsim_unit_registers_s *next;
} llsim_unit_registers_t;

/*
 * memory
 */
typedef struct llsim_memory_s {
	int entry_size;
	int bits;
	int height;
	int dp;
	int *data;
	char *name;

	int read;
	int read_addr;
	int write;
	int write_addr;
	int *datain;
	int *dataout;

	struct llsim_memory_s *next;
} llsim_memory_t;

typedef struct llsim_register_s {
	char *unit_name;
	char *reg_name;
	int bits;
	int reset_value;
	void *oldp;
	void *newp;
	struct llsim_register_s *next;
} llsim_register_t;

typedef struct llsim_output_s {
	char *unit_name;
	char *output_name;
	int bits;
	void *oldp;
	void *newp;
	struct llsim_output_s *next;
} llsim_output_t;

typedef struct llsim_input_s {
	char *unit_name;
	char *input_name;
	int bits;
	void *oldp;
	void *newp;
	struct llsim_input_s *next;
} llsim_input_t;

/*
 * simulated unit
 */
typedef struct llsim_unit_s {
	char *name;
	void (*run) (struct llsim_unit_s *unit);
	llsim_unit_registers_t *regs;
	void *private;
	llsim_memory_t *mems;
	llsim_register_t *registers;
	llsim_output_t *outputs;
	llsim_input_t *inputs;
	struct llsim_unit_s *next;
} llsim_unit_t;

/*
 * chip simulator main structure
 */
typedef struct llsim_s {
	llsim_unit_t *units;
	int clock;
	int reset;
} llsim_t;

llsim_t *llsim;

void *llsim_malloc(int len);
llsim_unit_t *llsim_register_unit(char *name, void (*run) (struct llsim_unit_s *unit));
llsim_unit_t *llsim_find_unit(char *name);
llsim_unit_registers_t *llsim_allocate_registers(llsim_unit_t *unit, char *name, int size);
int generic_extract_bits(char *p, int msb, int lsb);
void generic_inject_bits(char *p, int data, int msb, int lsb);
void llsim_register_register(char *unit_name, char *reg_name, int bits, int reset_value, void *oldp, void *newp);
void llsim_register_wire(char *unit_name, char *wire_name, int bits, void *wirep);
void llsim_register_output(char *unit_name, char *output_name, int bits, void *oldp, void *newp);
void llsim_register_input(char *unit_name, char *input_name, int bits, void *oldp, void *newp);
void llsim_stop(void);

/*
 * memories
 */
llsim_memory_t *llsim_allocate_memory(llsim_unit_t *unit, char *name, int bits, int height, int dp);
void llsim_mem_inject(llsim_memory_t *memory, int addr, int val, int msb, int lsb);
int llsim_mem_extract(llsim_memory_t *memory, int addr, int msb, int lsb);
void llsim_mem_set_datain(llsim_memory_t *memory, int val, int msb, int lsb);
void llsim_mem_write(llsim_memory_t *memory, int addr);
void llsim_mem_read(llsim_memory_t *memory, int addr);
int llsim_mem_extract_dataout(llsim_memory_t *memory, int msb, int lsb);
void llsim_run_clock(void);
#endif
