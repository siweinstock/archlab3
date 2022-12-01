#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "llsim.h"

/*
 * chip simulator
 */
llsim_t *llsim = NULL;
static int stop_sim = 0;

void *llsim_malloc(int len)
{
	void *p;

	p = (void *) malloc(len);
	llsim_assert(p != NULL, "out of memory");
	memset(p, 0, len);
	return p;
}

/*
 * unit registration functions
 */
llsim_unit_t *llsim_register_unit(char *name, void (*run) (struct llsim_unit_s *unit))
{
	llsim_unit_t *unit;

	unit = (llsim_unit_t *) llsim_malloc(sizeof(llsim_unit_t));
	unit->name = llsim_malloc(strlen(name)+1);
	strcpy(unit->name, name);
	unit->run = run;
	unit->next = llsim->units;
	unit->regs = NULL;
	llsim->units = unit;
	return unit;
}

llsim_unit_t *llsim_find_unit(char *name)
{
	llsim_unit_t *unit;

	unit = llsim->units;
	while (unit) {
		if (strcmp(name, unit->name) == 0)
			break;
		unit = unit->next;
	}
	return unit;
}

llsim_unit_registers_t *llsim_allocate_registers(llsim_unit_t *unit, char *name, int size)
{
	llsim_unit_registers_t *ur;

	ur = (llsim_unit_registers_t *) llsim_malloc(sizeof(llsim_unit_registers_t));
	ur->name = (char *) llsim_malloc(strlen(name)+1);
	strcpy(ur->name, name);
	ur->size = size;
	ur->old = (void *) llsim_malloc(size);
	ur->new = (void *) llsim_malloc(size);
	ur->next = unit->regs;
	unit->regs = ur;
	return ur;
}

void llsim_register_register(char *unit_name, char *reg_name, int bits, int reset_value, void *oldp, void *newp)
{
	llsim_unit_t *unit;
	llsim_register_t *reg, *p;

	unit = llsim_find_unit(unit_name);
	llsim_assert(unit != NULL, "ERROR: couldn't find unit %s", unit_name);

	reg = (llsim_register_t *) llsim_malloc(sizeof(llsim_register_t));
	reg->unit_name = (char *) llsim_malloc(strlen(unit_name)+1);
	strcpy(reg->unit_name, unit_name);
	reg->reg_name = (char *) llsim_malloc(strlen(reg_name)+1);
	strcpy(reg->reg_name, reg_name);
	reg->bits = bits;
	reg->reset_value = reset_value;
	reg->oldp = oldp;
	reg->newp = newp;
	reg->next = NULL;
	if (!unit->registers) {
		unit->registers = reg;
	} else {
		p = unit->registers;
		while (p->next)
			p = p->next;
		p->next = reg;
	}
}

void llsim_register_wire(char *unit_name, char *wire_name, int bits, void *wirep)
{
	// FIXME
}

void llsim_register_output(char *unit_name, char *output_name, int bits, void *oldp, void *newp)
{
	llsim_unit_t *unit;
	llsim_output_t *output, *p;

	unit = llsim_find_unit(unit_name);
	llsim_assert(unit != NULL, "ERROR: couldn't find unit %s", unit_name);

	output = (llsim_output_t *) llsim_malloc(sizeof(llsim_output_t));
	output->unit_name = (char *) llsim_malloc(strlen(unit_name)+1);
	strcpy(output->unit_name, unit_name);
	output->output_name = (char *) llsim_malloc(strlen(output_name)+1);
	strcpy(output->output_name, output_name);
	output->bits = bits;
	output->oldp = oldp;
	output->newp = newp;
	output->next = NULL;
	if (!unit->outputs) {
		unit->outputs = output;
	} else {
		p = unit->outputs;
		while (p->next)
			p = p->next;
		p->next = output;
	}
}

void llsim_register_input(char *unit_name, char *input_name, int bits, void *oldp, void *newp)
{
	llsim_unit_t *unit;
	llsim_input_t *input, *p;

	unit = llsim_find_unit(unit_name);
	llsim_assert(unit != NULL, "ERROR: couldn't find unit %s", unit_name);

	input = (llsim_input_t *) llsim_malloc(sizeof(llsim_input_t));
	input->unit_name = (char *) llsim_malloc(strlen(unit_name)+1);
	strcpy(input->unit_name, unit_name);
	input->input_name = (char *) llsim_malloc(strlen(input_name)+1);
	strcpy(input->input_name, input_name);
	input->bits = bits;
	input->oldp = oldp;
	input->newp = newp;
	input->next = NULL;
	if (!unit->inputs) {
		unit->inputs = input;
	} else {
		p = unit->inputs;
		while (p->next)
			p = p->next;
		p->next = input;
	}
}

int generic_extract_bits(char *p, int msb, int lsb)
{
	int byte_pos;
	i64 *p64, val64;

	byte_pos = lsb / 8;

	p64 = (i64 *) (p + byte_pos);
	val64 = lsbs(*p64, msb - byte_pos * 8, lsb - byte_pos * 8);
	return (int) val64;
}

void generic_inject_bits(char *p, int data, int msb, int lsb)
{
	int byte_pos;
	i64 *p64;

	byte_pos = lsb / 8;
	p64 = (i64 *) (p + byte_pos);
	*p64 = lrbs(*p64, data, msb - byte_pos * 8, lsb - byte_pos * 8);
}

/*
 * memories
 */
llsim_memory_t *llsim_allocate_memory(llsim_unit_t *unit, char *name, int bits, int height, int dp)
{
	llsim_memory_t *mem;

	llsim_assert(bits <= 32, "ERROR: bits %d not supported", bits);
	mem = (llsim_memory_t *) llsim_malloc(sizeof(llsim_memory_t));
	mem->entry_size = (bits + 31) / 32;
	mem->name = (char *) llsim_malloc(strlen(name)+1);
	strcpy(mem->name, name);
	mem->bits = bits;
	mem->height = height;
	mem->dp = dp;
	mem->data = (int *) llsim_malloc((1+height) * mem->entry_size * sizeof(int));
	mem->datain = (int *) llsim_malloc(mem->entry_size);
	mem->dataout = (int *) llsim_malloc(mem->entry_size);
	mem->next = unit->mems;
	unit->mems = mem;
	return mem;
}

void llsim_mem_inject(llsim_memory_t *memory, int addr, int val, int msb, int lsb)
{
	int *p;

	p = memory->data + addr * memory->entry_size;
	generic_inject_bits((char *) p, val, msb, lsb);
}

int llsim_mem_extract(llsim_memory_t *memory, int addr, int msb, int lsb)
{
	int *p;

	p = memory->data + addr * memory->entry_size;
	return generic_extract_bits((char *) p,msb,lsb);
}

void llsim_mem_write(llsim_memory_t *memory, int addr)
{
	llsim_assert(!memory->write, "ERROR: multiple memory writes to memory %s", memory->name);
	memory->write = 1;
	memory->write_addr = addr;
}

void llsim_mem_read(llsim_memory_t *memory, int addr)
{
	llsim_assert(!memory->read, "ERROR: multiple memory reads to memory %s", memory->name);
	memory->read = 1;
	memory->read_addr = addr;
}

void llsim_mem_set_datain(llsim_memory_t *memory, int val, int msb, int lsb)
{
	int *p;

	llsim_assert(msb <= 31 && lsb <= 31, "ERROR only <=32 bit memories supported");
	p = (int *) memory->datain;
	*p = rbs(*p,val,msb,lsb);
}

int llsim_mem_extract_dataout(llsim_memory_t *memory, int msb, int lsb)
{
	int *p;

	llsim_assert(msb <= 31 && lsb <= 31, "ERROR only <=32 bit memories supported");
	p = (int *) memory->dataout;
	return sbs(*p,msb,lsb);
}

void llsim_run_clock(void)
{
	llsim_unit_t *unit;
	llsim_unit_registers_t *ur;
	llsim_memory_t *mem;
	int read_done, write_done;
	
	/*
	 * run units
	 */
	unit = llsim->units;
	while (unit) {
		unit->run(unit);

		// memories
		mem = unit->mems;
		while (mem) {
			read_done = mem->read;
			write_done = mem->write;
			if (mem->read) {
				llsim_assert(mem->read_addr < mem->height, "mem %s read address %d out of range\n", mem->name, mem->read_addr);
				*mem->dataout = mem->data[mem->read_addr];
				llsim_printf("llsim: clock %d: READ MEM %s addr %d --> %08x\n", llsim->clock, mem->name, mem->read_addr, *mem->dataout);
				mem->read = 0;
			}
			if (mem->write) {
				llsim_assert(mem->write_addr < mem->height, "mem %s write address %d out of range\n", mem->name, mem->write_addr);
				mem->data[mem->write_addr] = *mem->datain;
				llsim_printf("llsim: clock %d: WRITE %08x --> MEM %s addr %d\n", llsim->clock, *mem->datain, mem->name, mem->write_addr);
				mem->write = 0;
			}
			llsim_assert(!(read_done && write_done), "ERROR: simultaneous access to memory %s", mem->name);
			if (!read_done && !write_done)
				*mem->dataout = 0xBAADBAAD;
			mem = mem->next;
		}
		unit = unit->next;
	}

	/*
	 * copy registers
	 */
	unit = llsim->units;
	while (unit) {
		ur = unit->regs;
		while (ur) {
			memcpy(ur->old, ur->new, ur->size);
			ur = ur->next;
		}
		unit = unit->next;
	}
}

static void llsim_init_units(char *program_name)
{
	llsim->units = NULL;
	llsim->clock = 0;
	sp_init(program_name);
}

static void llsim_init(char *program_name)
{
	llsim = llsim_malloc(sizeof(llsim_t));
	llsim_init_units(program_name);
}

static void llsim_init_reset_values(void)
{
	llsim_unit_t *unit;
	llsim_register_t *reg;

	/*
	 * run units
	 */
	unit = llsim->units;
	while (unit) {
		reg = unit->registers;
		while (reg) {
			* (int *) reg->newp = reg->reset_value;
			reg = reg->next;
		}
		unit = unit->next;
	}
}

void llsim_stop(void)
{
	stop_sim = 1;
}

int main(int argc, char **argv)
{
	int i;

	llsim_init(argv[1]);

	llsim_printf("llsim: starting simulation\n");
	llsim->reset = 1;

	// init registers
	llsim_init_reset_values();

	for (i = 0; i < 5; i++) {
		llsim_run_clock();
		llsim->clock++;
	}
	llsim->reset = 0;
	while (!stop_sim) {
		printf(">>>>> clock %d <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<\n", llsim->clock);
		llsim_run_clock();
		llsim->clock++;
		/*
		if ((llsim->clock % 1000000) == 0)
			printf("clock %d\n", llsim->clock);
		*/
	}
	return 0;
}

