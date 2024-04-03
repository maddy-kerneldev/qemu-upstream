/*
 * Qtrace writer plugin
 *
 * Copyright (C) 2024 Madhavan Srinivasan <maddy@linux.ibm.com>, IBM
 *
 * Based on the Qtrace writer library by Anton Blanchard
 * https://github.com/antonblanchard/qtrace-tools/blob/master/qtlib/qtwriter.c
 *
 * TCG plugin still has too many TODOs like
 * - Application Trigger to start/stop trace (currently STARTNOP/STOPNOP used)
 * - Handling traces in multiple Threads/Cores
 * - Input parameter option control
 * - Really bad at memory usage (plugin uses too much of memory at this point)
 * - ....
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version
 * 2 of the License, or (at your option) any later version.
 */
#define _GNU_SOURCE
#include <glib.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdint.h>
#include <stdbool.h>
#include <fcntl.h>
#include <errno.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/mman.h>
#include <assert.h>
#include <qemu-plugin.h>

#include "qtrace.h"

//Qtrace specific macros

#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
#define be16_to_cpup(A)	__builtin_bswap16(*(uint16_t *)(A))
#define be32_to_cpup(A)	__builtin_bswap32(*(uint32_t *)(A))
#define be64_to_cpup(A)	__builtin_bswap64(*(uint64_t *)(A))
#define cpu_to_be16(A) __builtin_bswap16(A)
#define cpu_to_be32(A) __builtin_bswap32(A)
#define cpu_to_be64(A) __builtin_bswap64(A)
#else
#define be16_to_cpup(A)	(*(uint16_t *)A)
#define be32_to_cpup(A)	(*(uint32_t *)A)
#define be64_to_cpup(A)	(*(uint64_t *)A)
#define cpu_to_be16(A) (A)
#define cpu_to_be32(A) (A)
#define cpu_to_be64(A) (A)
#endif

struct qtwriter_state {
	uint32_t version;
	uint32_t magic;
	struct qtrace_record prev_record;
	bool header_written;
	int fd;
	void *mem;
	size_t size;
	void *ptr;
};

/*
 * Qtrace writer functions/macros starts here
 */

#define QTWRITER_VERSION 0x7010000

/*
 * This needs to be bigger than the maximum qtrace record size. We also
 * want it to be large enough that we don't continually extend the file
 * with fallocate/mremap.
 */
#define BUFFER	(128*1024)

static struct qtwriter_state qtwr;

static int fallocate_or_ftruncate(int fd, size_t size)
{
	if (fallocate(fd, 0, 0, size) == 0)
		return 0;

	if (errno != EOPNOTSUPP)
		return -1;

	if (ftruncate(fd, size) == -1)
		return -1;

	return 0;
}

bool qtwriter_open(struct qtwriter_state *state, char *filename,
		   uint32_t magic)
{
	void *p;

	memset(state, 0, sizeof(*state));

	state->magic = magic;
	state->version = QTWRITER_VERSION;

	state->fd = open(filename, O_RDWR|O_CREAT|O_TRUNC, 0644);
	if (state->fd == -1) {
		perror("open");
		return false;
	}

	state->size = BUFFER;

	if (fallocate_or_ftruncate(state->fd, state->size) == -1) {
		perror("fallocate/ftruncate");
		return false;
	}

	p = mmap(NULL, state->size, PROT_READ|PROT_WRITE, MAP_SHARED,
		 state->fd, 0);

	if (p == MAP_FAILED) {
		perror("mmap");
		return false;
	}

	state->mem = p;
	state->ptr = state->mem;

	return true;
}

static inline void put8(struct qtwriter_state *state, uint8_t val)
{
	typeof(val) *p = state->ptr;
	*p = val;
	state->ptr += sizeof(*p);
}

static inline void put16(struct qtwriter_state *state, uint16_t val)
{
	typeof(val) *p = state->ptr;
	*p = cpu_to_be16(val);
	state->ptr += sizeof(*p);
}

static inline void put32(struct qtwriter_state *state, uint32_t val)
{
	typeof(val) *p = state->ptr;
	*p = cpu_to_be32(val);
	state->ptr += sizeof(*p);
}

static inline void put64(struct qtwriter_state *state, uint64_t val)
{
	typeof(val) *p = state->ptr;
	*p = cpu_to_be64(val);
	state->ptr += sizeof(*p);
}

/*
 * The header contains the address of the first instruction, so we can't
 * write it until we get the first trace entry.
 */
static bool qtwriter_write_header(struct qtwriter_state *state,
				  struct qtrace_record *record)
{
	uint16_t hdr_flags, flags, flags2, flags3;
	bool have_ptes = false;

	/* Header is identified by a zero instruction */
	put32(state, 0);

	flags = QTRACE_EXTENDED_FLAGS_PRESENT;
	put16(state, flags);

	flags2 = QTRACE_FILE_HEADER_PRESENT;

	if (record->radix_insn.nr_ptes)
		flags2 |= QTRACE_EXTENDED_FLAGS2_PRESENT;

	put16(state, flags2);

	flags3 = 0;
	if (record->radix_insn.nr_ptes && record->radix_insn.nr_pte_walks == 1) {
		assert(record->radix_insn.nr_pte_walks == 1);
		have_ptes = true;
		if (record->radix_insn.type == GUEST_REAL)
			flags3 |= (QTRACE_XLATE_MODE_RADIX << QTRACE_HOST_XLATE_MODE_INSTRUCTION_SHIFT) |
				  (QTRACE_XLATE_MODE_REAL << QTRACE_GUEST_XLATE_MODE_INSTRUCTION_SHIFT);
		else if (record->radix_insn.type == HOST_RADIX)
			flags3 |= (QTRACE_XLATE_MODE_RADIX << QTRACE_HOST_XLATE_MODE_INSTRUCTION_SHIFT) |
				  (QTRACE_XLATE_MODE_NOT_DEFINED << QTRACE_GUEST_XLATE_MODE_INSTRUCTION_SHIFT);
		else
			assert(0);
	} else if (record->radix_insn.nr_ptes && record->radix_insn.nr_pte_walks > 1) {
		assert(record->radix_insn.nr_ptes <= NR_RADIX_PTES);
		assert(record->radix_insn.nr_pte_walks <= MAX_RADIX_WALKS);
		assert(record->radix_insn.nr_pte_walks > 0);
		have_ptes = true;
		flags3 |= (QTRACE_XLATE_MODE_RADIX << QTRACE_HOST_XLATE_MODE_INSTRUCTION_SHIFT) |
				    (QTRACE_XLATE_MODE_RADIX << QTRACE_GUEST_XLATE_MODE_INSTRUCTION_SHIFT);
	}

	if (have_ptes)
		put16(state, flags3);

	hdr_flags = QTRACE_HDR_IAR_PRESENT;

	if (record->insn_ra_valid)
		hdr_flags |= QTRACE_HDR_IAR_RPN_PRESENT;

	if (record->insn_page_shift_valid)
		hdr_flags |= QTRACE_HDR_IAR_PAGE_SIZE_PRESENT;

	if (record->guest_insn_page_shift_valid)
		hdr_flags |= QTRACE_HDR_IAR_GPAGE_SIZE_PRESENT;

	if (state->version)
		hdr_flags |= QTRACE_HDR_VERSION_NUMBER_PRESENT;

	if (state->magic)
		hdr_flags |= QTRACE_HDR_MAGIC_NUMBER_PRESENT;

	put16(state, hdr_flags);

	if (state->magic)
		put32(state, state->magic);

	if (state->version)
		put32(state, state->version);

	put64(state, record->insn_addr);


	if (have_ptes) {
		int nr_walks = 1;
		int nr_ptes = NR_RADIX_PTES;

		if (record->radix_insn.nr_pte_walks > 1) {
			nr_walks = record->radix_insn.nr_pte_walks;
			nr_ptes = record->radix_insn.nr_ptes;
			put8(state, record->radix_insn.nr_ptes);
			put8(state, record->radix_insn.nr_pte_walks);
		}

		for (int j = 0; j < nr_walks; j++)
			for (int i = 0; i < nr_ptes; i++)
				put64(state, record->radix_insn.host_ptes[j][i]);

		if (record->radix_insn.nr_pte_walks > 1) {
			for (int i = 0; i < record->radix_insn.nr_pte_walks - 1; i++)
				put64(state, record->radix_insn.host_real_addrs[i]);

			for (int i = 0; i < record->radix_insn.nr_pte_walks; i++)
				put64(state, record->radix_insn.guest_real_addrs[i]);
		}
	}

	if (record->insn_ra_valid) {
		uint8_t pshift = 16;

		if (record->insn_page_shift_valid)
			pshift = record->insn_page_shift;

		put32(state, record->insn_ra >> pshift);
	}

	if (record->insn_page_shift_valid)
		put8(state, record->insn_page_shift);

	if (record->guest_insn_page_shift_valid)
		put8(state, record->guest_insn_page_shift);

	return true;
}

bool qtwriter_write_record(struct qtwriter_state *state,
			   struct qtrace_record *record)
{
	uint16_t flags;
	uint16_t flags2;
	uint16_t flags3;
	bool iar_change = false;
	bool is_branch = false;
	bool have_flags3 = false;
	bool have_insn_ptes = false;
	bool have_data_ptes = false;

	/* Do we need to allocate more space? */
	if ((state->ptr + BUFFER) > (state->mem + state->size)) {
		void *p;
		size_t offset;

		if (fallocate_or_ftruncate(state->fd, state->size + BUFFER) == -1) {
			perror("fallocate/ftruncate");
			return false;
		}

		p = mremap(state->mem, state->size, state->size + BUFFER,
			   MREMAP_MAYMOVE);
		if (p == MAP_FAILED) {
			perror("mmap");
			return false;
		}

		state->size += BUFFER;
		offset = state->ptr - state->mem;

		state->mem = p;

		/* adjust ->ptr, mremap may have returned a new address */
		state->ptr = state->mem + offset;
	}

	if (state->header_written == false) {
		qtwriter_write_header(state, record);
		state->header_written = true;

		memcpy(&state->prev_record, record, sizeof(*record));

		return true;
	}

	flags = QTRACE_EXTENDED_FLAGS_PRESENT;

	flags2 = 0;
	flags3 = 0;

	/* Some sort of branch */
	if (state->prev_record.branch == true ||
	    record->insn_addr != (state->prev_record.insn_addr + 4))
		is_branch = true;

	if ((record->insn_addr != (state->prev_record.insn_addr + 4)))
		iar_change = true;

	if (state->prev_record.data_addr_valid)
		flags |= QTRACE_DATA_ADDRESS_PRESENT;

	if (state->prev_record.data_ra_valid) {
		flags |= QTRACE_DATA_RPN_PRESENT;

		if (state->prev_record.radix_data.nr_ptes && state->prev_record.radix_data.nr_pte_walks == 1) {
			assert(state->prev_record.radix_data.nr_pte_walks == 1);
			have_flags3 = true;
			have_data_ptes = true;
			flags2 |= QTRACE_EXTENDED_FLAGS2_PRESENT;
			flags3 |= QTRACE_XLATE_MODE_RADIX << QTRACE_HOST_XLATE_MODE_DATA_SHIFT;
			if (state->prev_record.radix_data.type == GUEST_REAL)
				flags3 |= QTRACE_XLATE_MODE_REAL << QTRACE_GUEST_XLATE_MODE_DATA_SHIFT;
			else if (state->prev_record.radix_data.type == HOST_RADIX)
				flags3 |= QTRACE_XLATE_MODE_NOT_DEFINED << QTRACE_GUEST_XLATE_MODE_DATA_SHIFT;
			else
				assert(0);
		} else if (state->prev_record.radix_data.nr_ptes && state->prev_record.radix_data.nr_pte_walks > 1) {
			assert(state->prev_record.radix_data.nr_ptes <= NR_RADIX_PTES);
			assert(state->prev_record.radix_data.nr_pte_walks <= MAX_RADIX_WALKS);
			assert(state->prev_record.radix_data.nr_pte_walks > 0);
			have_flags3 = true;
			have_data_ptes = true;
			flags2 |= QTRACE_EXTENDED_FLAGS2_PRESENT;
			flags3 |= QTRACE_XLATE_MODE_RADIX << QTRACE_HOST_XLATE_MODE_DATA_SHIFT;
			flags3 |= QTRACE_XLATE_MODE_RADIX << QTRACE_GUEST_XLATE_MODE_DATA_SHIFT;
		}
	}

	if (state->prev_record.data_page_shift_valid)
		flags2 |= QTRACE_DATA_PAGE_SIZE_PRESENT;

	if (state->prev_record.guest_data_page_shift_valid)
		flags2 |= QTRACE_DATA_GPAGE_SIZE_PRESENT;

	if (record->insn_ra_valid && iar_change) {
		flags |= QTRACE_IAR_RPN_PRESENT;

		if (record->radix_insn.nr_ptes && record->radix_insn.nr_pte_walks == 1) {
			assert(record->radix_insn.nr_pte_walks == 1);
			have_flags3 = true;
			have_insn_ptes = true;
			flags2 |= QTRACE_EXTENDED_FLAGS2_PRESENT;
			flags3 |= QTRACE_XLATE_MODE_RADIX << QTRACE_HOST_XLATE_MODE_INSTRUCTION_SHIFT;
			flags3 |= QTRACE_XLATE_MODE_NOT_DEFINED << QTRACE_GUEST_XLATE_MODE_INSTRUCTION_SHIFT;
			if (record->radix_insn.type == GUEST_REAL)
				flags3 |= QTRACE_XLATE_MODE_REAL << QTRACE_GUEST_XLATE_MODE_DATA_SHIFT;
			else if (record->radix_insn.type == HOST_RADIX)
				flags3 |= QTRACE_XLATE_MODE_NOT_DEFINED << QTRACE_GUEST_XLATE_MODE_DATA_SHIFT;
			else
				assert(0);
		} else if (record->radix_insn.nr_ptes && record->radix_insn.nr_pte_walks > 1) {
			assert(record->radix_insn.nr_ptes <= NR_RADIX_PTES);
			assert(record->radix_insn.nr_pte_walks <= MAX_RADIX_WALKS);
			assert(record->radix_insn.nr_pte_walks > 0);
			have_flags3 = true;
			have_insn_ptes = true;
			flags2 |= QTRACE_EXTENDED_FLAGS2_PRESENT;
			flags3 |= QTRACE_XLATE_MODE_RADIX << QTRACE_HOST_XLATE_MODE_INSTRUCTION_SHIFT;
			flags3 |= QTRACE_XLATE_MODE_RADIX << QTRACE_GUEST_XLATE_MODE_INSTRUCTION_SHIFT;
		}
	}

	if (record->insn_page_shift_valid && iar_change)
		flags2 |= QTRACE_IAR_PAGE_SIZE_PRESENT;

	if (record->guest_insn_page_shift_valid && iar_change)
		flags2 |= QTRACE_INSTRUCTION_GPAGE_SIZE_PRESENT;

	if (is_branch) {
		flags |= QTRACE_NODE_PRESENT | QTRACE_TERMINATION_PRESENT;

		if (iar_change)
			flags |= (QTRACE_IAR_CHANGE_PRESENT | QTRACE_IAR_PRESENT);
	}

	put32(state, state->prev_record.insn);

	put16(state, flags);

	put16(state, flags2);

	if (have_flags3) {
		put16(state, flags3);
	}

	if (is_branch) {
		uint8_t termination_code = 0;

		/* node */
		put8(state, 0);

		/* termination node */
		put8(state, 0);

		/* termination code */
		if (state->prev_record.branch) {
			if (state->prev_record.conditional_branch == true)
				//termination_code = QTRACE_EXCEEDED_MAX_INST_DEPTH;
				termination_code = QTRACE_EXCEEDED_MAX_BRANCH_DEPTH;
			else
				termination_code = QTRACE_UNCONDITIONAL_BRANCH;
		} else {
			termination_code = QTRACE_EXCEPTION;
		}

		put8(state, termination_code);
	}

	if (state->prev_record.data_addr_valid)
		put64(state, state->prev_record.data_addr);


	if (state->prev_record.data_ra_valid) {
		uint8_t pshift = 16;

		if (have_data_ptes) {
			int nr_walks = 1;
			int nr_ptes = NR_RADIX_PTES;

			if (state->prev_record.radix_data.nr_pte_walks > 1) {
				nr_walks = state->prev_record.radix_data.nr_pte_walks;
				nr_ptes = state->prev_record.radix_data.nr_ptes;
				put8(state, state->prev_record.radix_data.nr_ptes);
				put8(state, state->prev_record.radix_data.nr_pte_walks);
			}

			for (int i = 0; i < nr_walks; i++)
				for (int j = 0; j < nr_ptes; j++)
					put64(state, state->prev_record.radix_data.host_ptes[i][j]);

			if (state->prev_record.radix_data.nr_pte_walks > 1) {
				for (int i = 0; i < state->prev_record.radix_data.nr_pte_walks - 1; i++)
					put64(state, state->prev_record.radix_data.host_real_addrs[i]);

				for (int i = 0; i < state->prev_record.radix_data.nr_pte_walks; i++)
					put64(state, state->prev_record.radix_data.guest_real_addrs[i]);
			}
		}


		if (state->prev_record.data_page_shift_valid)
			pshift = state->prev_record.data_page_shift;

		put32(state, state->prev_record.data_ra >> pshift);
	}

	if (iar_change)
		put64(state, record->insn_addr);

	if (have_insn_ptes) {
		int nr_walks = 1;
		int nr_ptes = NR_RADIX_PTES;

		if (record->radix_insn.nr_pte_walks > 1) {
			nr_walks = record->radix_insn.nr_pte_walks;
			nr_ptes = record->radix_insn.nr_ptes;
			put8(state, record->radix_insn.nr_ptes);
			put8(state, record->radix_insn.nr_pte_walks);
		}

		for (int i = 0; i < nr_walks; i++)
			for (int j = 0; j < nr_ptes; j++)
				put64(state, record->radix_insn.host_ptes[i][j]);

		if (record->radix_insn.nr_pte_walks > 1) {
			for (int i = 0; i < record->radix_insn.nr_pte_walks - 1; i++)
				put64(state, record->radix_insn.host_real_addrs[i]);

			for (int i = 0; i < record->radix_insn.nr_pte_walks; i++)
				put64(state, record->radix_insn.guest_real_addrs[i]);
		}
	}

	if (record->insn_ra_valid && iar_change) {
		uint8_t pshift = 16;

		if (record->insn_page_shift_valid)
			pshift = record->insn_page_shift;

		put32(state, record->insn_ra >> pshift);
	}

	/* XXX Add sequential insn rpn and sequential page size */

	if (record->insn_page_shift_valid && iar_change)
		put8(state, record->insn_page_shift);

	if (record->guest_insn_page_shift_valid && iar_change)
		put8(state, record->guest_insn_page_shift);

	if (state->prev_record.data_page_shift_valid)
		put8(state, state->prev_record.data_page_shift);

	if (state->prev_record.guest_data_page_shift_valid)
		put8(state, state->prev_record.guest_data_page_shift);


	memcpy(&state->prev_record, record, sizeof(*record));

	return true;
}

#if 0
void qtwriter_write_record_simple(struct qtwriter_state *state, uint32_t insn,
				  unsigned long insn_addr)
{
	struct qtrace_record record;

	memset(&record, 0, sizeof(record));

	record.insn = insn;
	record.insn_addr = insn_addr;

	/* what about branches? */

	qtwriter_write_record(state, &record);
}

void qtwriter_write_storage_record_simple(struct qtwriter_state *state,
					  uint32_t insn, unsigned long insn_addr,
					  unsigned long storage_addr,
					  unsigned long storage_size)
{
	struct qtrace_record record;

	memset(&record, 0, sizeof(record));

	record.insn = insn;
	record.insn_addr = insn_addr;

	record.data_addr_valid = true;
	record.data_addr = storage_addr;

	/* what about branches? */

	qtwriter_write_record(state, &record);
}
#endif

void qtwriter_close(struct qtwriter_state *state)
{
	struct qtrace_record record;

	/* Flush the final instruction */
	memset(&record, 0, sizeof(record));
	record.insn_addr = state->prev_record.insn_addr + 4;
	qtwriter_write_record(state, &record);

	munmap(state->mem, state->size);

	/* truncate file to actual size */
	if (ftruncate(state->fd, state->ptr - state->mem)) {
		fprintf(stderr, "ftruncate\n");
	}

	close(state->fd);
}

#define CACHELINE_SIZE 128

#define PPC_FIELD(value, from, len) \
	(((value) >> (32 - (from) - (len))) & ((1 << (len)) - 1))
#define PPC_SEXT(v, bs) \
	((((unsigned long) (v) & (((unsigned long) 1 << (bs)) - 1)) \
	  ^ ((unsigned long) 1 << ((bs) - 1))) \
	 - ((unsigned long) 1 << ((bs) - 1)))

#define PPC_OPC(insn)	PPC_FIELD(insn, 0, 6)
#define PPC_RT(insn)	PPC_FIELD(insn, 6, 5)
#define PPC_RA(insn)	PPC_FIELD(insn, 11, 5)
#define PPC_RB(insn)	PPC_FIELD(insn, 16, 5)
#define PPC_NB(insn)	PPC_FIELD(insn, 16, 5)
#define PPC_D(insn)	PPC_SEXT(PPC_FIELD(insn, 16, 16), 16)
#define PPC_DS(insn)	PPC_SEXT(PPC_FIELD(insn, 16, 14), 14)
#define PPC_DQ(insn)	PPC_SEXT(PPC_FIELD(insn, 16, 12), 12)

bool is_storage_insn(uint32_t insn)
{
	int opcode = PPC_OPC(insn);

	switch (opcode) {
	case 31 ... 58:
		return true;
	case 61:
	case 62:
		return true;
	}

	return false;
}

/*
 * QEMU TCG Plugin starts here
 */

QEMU_PLUGIN_EXPORT int qemu_plugin_version = QEMU_PLUGIN_VERSION;
static enum qemu_plugin_mem_rw rw = QEMU_PLUGIN_MEM_RW;


/* Store last executed instruction on each vCPU as a GString */
GArray *last_exec;

typedef struct {
	uint32_t opcode;
	char *disas_str;
	const char *symbol;
	uint64_t addr;
	uint64_t vaddr;
	uint64_t haddr;
	uint64_t d_vaddr;
	uint64_t d_haddr;
}insn_info;

// This flag is a optimization to enable the check in exec_cb code
static bool spl_detect;
static bool gdump_flag;

int nostorage_write_qtrecord(insn_info *ptr)
{
	struct qtrace_record qtr;
	uint32_t insn = ptr->opcode;

	memset(&qtr, 0, sizeof(qtr));

	/*
	 * Update qt_record with instruction details
	 */
	qtr.insn = insn;
	qtr.insn_addr = ptr->vaddr;
	qtr.branch = is_branch(insn);
	qtr.conditional_branch = is_conditional_branch(insn);

	qtwriter_write_record(&qtwr, &qtr);

	return 0;
}

int storage_write_qtrecord(insn_info *ptr)
{
	struct qtrace_record qtr;
	uint32_t insn = ptr->opcode;

	memset(&qtr, 0, sizeof(qtr));

	/*
	 * Update qt_record with instruction details
	 */
	qtr.insn = insn;
	qtr.insn_addr = ptr->vaddr;
	qtr.data_addr = ptr->d_vaddr;
	qtr.data_addr_valid = true;
	qtr.branch = is_branch(insn);
	qtr.conditional_branch = is_conditional_branch(insn);

	qtwriter_write_record(&qtwr, &qtr);

	return 0;
}

static void vcpu_insn_mem_access(unsigned int vcpu_index, qemu_plugin_meminfo_t info,
					uint64_t vaddr, void *udata)
{
	insn_info *inst = (insn_info *)udata;
	struct qemu_plugin_hwaddr *hwaddr;
	uint64_t vaddr1 = inst->vaddr;
	uint64_t haddr=0;
	g_autoptr(GString)rep = g_string_new("");

	hwaddr = qemu_plugin_get_hwaddr(info, vaddr);
	haddr = hwaddr ? qemu_plugin_hwaddr_phys_addr(hwaddr) : 0;
	inst->d_vaddr = vaddr;
	inst->d_haddr = haddr;
	if(gdump_flag) {
		g_string_append_printf(rep, "M14: mem:disasm %s vaddr 0x%lx(0x%lx) haddr 0x%lx\n",
				inst->disas_str, vaddr, vaddr1, haddr);
		qemu_plugin_outs(rep->str);
		storage_write_qtrecord(inst);
	}
}

static void vcpu_insn_exec(unsigned int cpu_index, void *udata)
{
	insn_info *inst = (insn_info *)udata;

	if (spl_detect) {
		if(g_str_has_prefix(inst->disas_str, "and r1, r1, r1"))
			gdump_flag = false;

		if(gdump_flag) {
			g_autoptr(GString)rep = g_string_new("");
			g_string_append_printf(rep, "M14: exec opcode 0x%x disasm %s vaddr 0x%lx haddr 0x%lx\n",
					inst->opcode, inst->disas_str, inst->vaddr, inst->addr);
			qemu_plugin_outs(rep->str);
			if(!is_storage_insn(inst->opcode))
				nostorage_write_qtrecord(inst);
		}

		if(g_str_has_prefix(inst->disas_str, "and r0, r0, r0"))
			gdump_flag = true;
	}
}

static void vcpu_tb_trans(qemu_plugin_id_t id, struct qemu_plugin_tb *tb)
{
	struct qemu_plugin_insn *insn;
	insn_info *inst;

	size_t n = qemu_plugin_tb_n_insns(tb);
	for (size_t i = 0; i < n; i++) {
		insn = qemu_plugin_tb_get_insn(tb, i);
		inst = g_new0(insn_info, 1);
		inst->disas_str = qemu_plugin_insn_disas(insn);
		if(g_str_has_prefix(inst->disas_str, "and r0, r0, r0"))
			spl_detect = true;
		inst->vaddr = qemu_plugin_insn_vaddr(insn);
		inst->opcode = *((uint32_t *)qemu_plugin_insn_data(insn));

		//Now based on spl_detect decide to register other call backs
		if (spl_detect) {
			qemu_plugin_register_vcpu_mem_cb(insn, vcpu_insn_mem_access,\
								QEMU_PLUGIN_CB_NO_REGS, rw, inst);
			qemu_plugin_register_vcpu_insn_exec_cb(insn, vcpu_insn_exec,\
								QEMU_PLUGIN_CB_NO_REGS,inst);
		}
	}
}

static void plugin_exit(qemu_plugin_id_t id, void *p)
{
	//Should free memory Here
	qtwriter_close(&qtwr);
}

/**
 * Install the plugin
 */
QEMU_PLUGIN_EXPORT int qemu_plugin_install(qemu_plugin_id_t id,
				const qemu_info_t *info, int argc,
				char **argv)
{
	/*
	* Initialize dynamic array to cache vCPU instruction. In user mode
	* we don't know the size before emulation.
	*/
	last_exec = g_array_new(FALSE, FALSE, sizeof(GString *));
	gdump_flag = false;
	spl_detect = false;

	qtwriter_open(&qtwr, "/tmp/inst_qtrace.qt", 0);

	/* Register translation block and exit callbacks */
	qemu_plugin_register_vcpu_tb_trans_cb(id, vcpu_tb_trans);
	qemu_plugin_register_atexit_cb(id, plugin_exit, NULL);

	return 0;
}
