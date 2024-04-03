#ifndef __QTRACE_H__
#define __QTRACE_H__

/* File header flags */
#define QTRACE_HDR_MAGIC_NUMBER_PRESENT			0x8000
#define QTRACE_HDR_VERSION_NUMBER_PRESENT		0x4000
#define QTRACE_HDR_IAR_PRESENT				0x2000
#define QTRACE_HDR_IAR_VSID_PRESENT			0x1000
#define QTRACE_HDR_IAR_RPN_PRESENT			0x0800
#define QTRACE_HDR_IAR_PAGE_SIZE_PRESENT		0x0040
#define QTRACE_HDR_IAR_GPAGE_SIZE_PRESENT		0x0010
#define QTRACE_HDR_COMMENT_PRESENT			0x0002

#define UNHANDLED_HDR_FLAGS	(~(QTRACE_HDR_MAGIC_NUMBER_PRESENT|QTRACE_HDR_VERSION_NUMBER_PRESENT|QTRACE_HDR_IAR_PRESENT|QTRACE_HDR_IAR_VSID_PRESENT|QTRACE_HDR_IAR_RPN_PRESENT|QTRACE_HDR_IAR_PAGE_SIZE_PRESENT|QTRACE_HDR_IAR_GPAGE_SIZE_PRESENT|QTRACE_HDR_COMMENT_PRESENT))

/* Primary flags */
#define QTRACE_IAR_CHANGE_PRESENT			0x8000
#define QTRACE_NODE_PRESENT				0x4000
#define QTRACE_TERMINATION_PRESENT			0x2000
#define QTRACE_PROCESSOR_PRESENT			0x1000
#define QTRACE_DATA_ADDRESS_PRESENT			0x0800
#define QTRACE_DATA_VSID_PRESENT			0x0400
#define QTRACE_DATA_RPN_PRESENT				0x0200
#define QTRACE_LENGTH_PRESENT				0x0100
#define QTRACE_DATA_PRESENT				0x0080
#define QTRACE_IAR_PRESENT				0x0040
#define QTRACE_IAR_VSID_PRESENT				0x0020
#define QTRACE_IAR_RPN_PRESENT				0x0010
#define QTRACE_REGISTER_TRACE_PRESENT			0x0008
#define QTRACE_EXTENDED_FLAGS_PRESENT			0x0001

#define UNHANDLED_FLAGS	(~(QTRACE_IAR_CHANGE_PRESENT|QTRACE_NODE_PRESENT|QTRACE_TERMINATION_PRESENT|QTRACE_PROCESSOR_PRESENT|QTRACE_DATA_ADDRESS_PRESENT|QTRACE_DATA_VSID_PRESENT|QTRACE_DATA_RPN_PRESENT|QTRACE_LENGTH_PRESENT|QTRACE_DATA_PRESENT|QTRACE_IAR_PRESENT|QTRACE_IAR_VSID_PRESENT|QTRACE_IAR_RPN_PRESENT|QTRACE_REGISTER_TRACE_PRESENT|QTRACE_EXTENDED_FLAGS_PRESENT))

/* First extended flags */
#define QTRACE_SEQUENTIAL_INSTRUCTION_RPN_PRESENT	0x4000
#define QTRACE_TRACE_ERROR_CODE_PRESENT			0x1000
#define QTRACE_IAR_PAGE_SIZE_PRESENT			0x0200
#define QTRACE_DATA_PAGE_SIZE_PRESENT			0x0100
#define QTRACE_SEQUENTIAL_INSTRUCTION_PAGE_SIZE_PRESENT	0x0020
#define QTRACE_INSTRUCTION_GPAGE_SIZE_PRESENT		0x0008
#define QTRACE_DATA_GPAGE_SIZE_PRESENT			0x0004
#define QTRACE_FILE_HEADER_PRESENT			0x0002
#define QTRACE_EXTENDED_FLAGS2_PRESENT			0x0001

#define UNHANDLED_FLAGS2	(~(QTRACE_SEQUENTIAL_INSTRUCTION_RPN_PRESENT|QTRACE_TRACE_ERROR_CODE_PRESENT|QTRACE_IAR_PAGE_SIZE_PRESENT|QTRACE_DATA_PAGE_SIZE_PRESENT|QTRACE_SEQUENTIAL_INSTRUCTION_PAGE_SIZE_PRESENT|QTRACE_INSTRUCTION_GPAGE_SIZE_PRESENT|QTRACE_DATA_GPAGE_SIZE_PRESENT|QTRACE_FILE_HEADER_PRESENT|QTRACE_EXTENDED_FLAGS2_PRESENT))

#define IS_RADIX(FLAGS2)	((FLAGS2) & QTRACE_EXTENDED_FLAGS2_PRESENT)

/* Second extended flags */
#define QTRACE_HOST_XLATE_MODE_DATA			0xC000
#define QTRACE_HOST_XLATE_MODE_DATA_SHIFT		14
#define QTRACE_GUEST_XLATE_MODE_DATA			0x3000
#define QTRACE_GUEST_XLATE_MODE_DATA_SHIFT		12
#define QTRACE_HOST_XLATE_MODE_INSTRUCTION		0x0C00
#define QTRACE_HOST_XLATE_MODE_INSTRUCTION_SHIFT	10
#define QTRACE_GUEST_XLATE_MODE_INSTRUCTION		0x0300
#define QTRACE_GUEST_XLATE_MODE_INSTRUCTION_SHIFT	8
#define QTRACE_PTCR_PRESENT				0x0080
#define QTRACE_LPID_PRESENT				0x0040
#define QTRACE_PID_PRESENT				0x0020

#define QTRACE_XLATE_MODE_MASK				0x3
#define QTRACE_XLATE_MODE_RADIX				0
#define QTRACE_XLATE_MODE_REAL				1
#define QTRACE_XLATE_MODE_HPT				2
#define QTRACE_XLATE_MODE_NOT_DEFINED			3

#define UNHANDLED_FLAGS3 0

/* Termination codes */
#define QTRACE_EXCEEDED_MAX_INST_DEPTH			0x40
#define QTRACE_EXCEEDED_MAX_BRANCH_DEPTH		0x80
#define QTRACE_EXCEPTION				0x10
#define QTRACE_UNCONDITIONAL_BRANCH			0x08

/* 4 level radix */
#define NR_RADIX_PTES	4
#define MAX_RADIX_WALKS 5

enum branch_type {
	BRANCH,
	CALL,
	RETURN,
	ADDRESSING,
	SYSTEM_CALL_EXCEPTION,
	ASYNC_EXCEPTION,
	EXCEPTION_RETURN
};

struct qtrace_register_info {
	uint16_t index;
	uint64_t value;
};

#define QTRACE_MAX_GPRS_OUT  32
#define QTRACE_MAX_FPRS_OUT   3
#define QTRACE_MAX_SPRS_OUT   4
#define QTRACE_MAX_VMXRS_OUT  3
#define QTRACE_MAX_VSXRS_OUT  3

struct qtrace_reg_state {
	uint8_t nr_gprs_in;
	uint8_t nr_fprs_in;
	uint8_t nr_vmxs_in;
	uint8_t nr_vsxs_in;
	uint8_t nr_sprs_in;
	uint8_t nr_gprs_out;
	uint8_t nr_fprs_out;
	uint8_t nr_vmxs_out;
	uint8_t nr_vsxs_out;
	uint8_t nr_sprs_out;
	struct qtrace_register_info gprs_in[QTRACE_MAX_GPRS_OUT];
	struct qtrace_register_info gprs_out[QTRACE_MAX_GPRS_OUT];
	struct qtrace_register_info fprs_in[QTRACE_MAX_FPRS_OUT];
	struct qtrace_register_info fprs_out[QTRACE_MAX_FPRS_OUT];
	struct qtrace_register_info sprs_in[QTRACE_MAX_SPRS_OUT];
	struct qtrace_register_info sprs_out[QTRACE_MAX_SPRS_OUT];
};

enum xlate_type {
	UNSPECIFIED,
	GUEST_REAL,
	HOST_RADIX
};

struct qtrace_radix {
	enum xlate_type type;
	unsigned int nr_ptes;
	unsigned int nr_pte_walks;
	uint64_t host_ptes[MAX_RADIX_WALKS][NR_RADIX_PTES];
	uint64_t host_real_addrs[MAX_RADIX_WALKS-1];
	uint64_t guest_real_addrs[MAX_RADIX_WALKS];
};

struct qtrace_record {
	uint32_t insn;
	uint64_t insn_addr;
	bool insn_ra_valid;
	uint64_t insn_ra;
	bool insn_page_shift_valid;
	uint32_t insn_page_shift;
	bool data_addr_valid;
	uint64_t data_addr;
	bool data_ra_valid;
	uint64_t data_ra;
	bool data_page_shift_valid;
	uint32_t data_page_shift;

	bool branch;
	bool conditional_branch;

	bool guest_insn_page_shift_valid;
	uint32_t guest_insn_page_shift;

	bool guest_data_page_shift_valid;
	uint32_t guest_data_page_shift;

	struct qtrace_radix radix_insn;

	struct qtrace_radix radix_data;


	/*
	 * The rest of the fields are populated by qtreader if enabled,
	 * but are not required by qtwriter.
	 */
	bool branch_taken;
	bool branch_direct;
	enum branch_type branch_type;

	struct qtrace_reg_state regs;

	bool tlbie;
	bool tlbie_local;
	uint8_t tlbie_ric;
	bool tlbie_prs;
	bool tlbie_r;
	uint8_t tlbie_is;
	uint16_t tlbie_set;
	uint32_t tlbie_page_shift;
	uint64_t tlbie_addr;
	uint32_t tlbie_lpid;
	uint32_t tlbie_pid;

	bool node_valid;
	uint8_t node;
	uint8_t term_code;
	uint8_t term_node;

	/* We might want to add BH target unpredictable and static branch hints */

	uint64_t next_insn_addr;
};

#define OPCODE(insn)            ((insn) >> 26)
#define SUB_OPCODE(insn)        (((insn) >> 1) & 0x3ff)
#define BO(insn)                (((insn) >> 21) & 0x1f)

#define BRANCH_ABSOLUTE 0x2

/*
 * A conditional branch is unconditional if the BO field is 0b1X1XX
 */
static bool branch_conditional_is_conditional(uint32_t insn)
{
	return !!((BO(insn) & 0x14) != 0x14);
}

static inline bool is_conditional_branch(uint32_t insn)
{
	uint32_t opcode = OPCODE(insn);

	if ((opcode == 16) && branch_conditional_is_conditional(insn))
		return true;

	if (opcode == 19) {
		uint32_t sub_opcode = SUB_OPCODE(insn);

		switch (sub_opcode) {
		case 16:	/* bclr */
		case 528:	/* bcctr */
		case 560:	/* bctar */
			if (branch_conditional_is_conditional(insn))
				return true;
			break;
		}
	}

	return false;
}

static inline bool is_unconditional_branch(uint32_t insn)
{
	uint32_t opcode = insn >> (32-6);

	if ((opcode == 16) && !branch_conditional_is_conditional(insn))
		return true;

	/* Include sc, scv */
	if (opcode == 17 || opcode == 18)
		return true;

	if (opcode == 19) {
		uint32_t sub_opcode = SUB_OPCODE(insn);

		switch (sub_opcode) {
		case 16:	/* bclr */
		case 528:	/* bcctr */
		case 560:	/* bctar */
			if (!branch_conditional_is_conditional(insn))
				return true;
			break;

		case 50:	/* rfi */
		case 18:	/* rfid */
		case 274:	/* hrfid */
		case 82:	/* rfscv */
			return true;
			break;
		}
	}

	return false;
}

static inline bool is_branch(uint32_t insn)
{
	if (is_conditional_branch(insn) || is_unconditional_branch(insn))
		return true;

	return false;
}

static inline bool is_offset_in_branch_range(long offset)
{
	/*
	 * Powerpc branch instruction is :
	 *
	 *  0         6                 30   31
	 *  +---------+----------------+---+---+
	 *  | opcode  |     LI         |AA |LK |
	 *  +---------+----------------+---+---+
	 *  Where AA = 0 and LK = 0
	 *
	 * LI is a signed 24 bits integer. The real branch offset is computed
	 * by: imm32 = SignExtend(LI:'0b00', 32);
	 *
	 * So the maximum forward branch should be:
	 *   (0x007fffff << 2) = 0x01fffffc =  0x1fffffc
	 * The maximum backward branch should be:
	 *   (0xff800000 << 2) = 0xfe000000 = -0x2000000
	 */
	return (offset >= -0x2000000 && offset <= 0x1fffffc && !(offset & 0x3));
}

static inline unsigned int create_branch(unsigned long addr,
			   unsigned long target, int flags)
{
	unsigned int instruction;
	long offset;

	offset = target;
	if (! (flags & BRANCH_ABSOLUTE))
		offset = offset - (unsigned long)addr;

	/* Check we can represent the target in the instruction format */
	if (!is_offset_in_branch_range(offset))
		return 0;

	/* Mask out the flags and target, so they don't step on each other. */
	instruction = 0x48000000 | (flags & 0x3) | (offset & 0x03FFFFFC);

	return instruction;
}

static inline unsigned int create_cond_branch(unsigned long addr,
				unsigned long target, int flags)
{
	unsigned int instruction;
	long offset;

	offset = target;
	if (! (flags & BRANCH_ABSOLUTE))
		offset = offset - (unsigned long)addr;

	/* Check we can represent the target in the instruction format */
	if (offset < -0x8000 || offset > 0x7FFF || offset & 0x3)
		return 0;

	/* Mask out the flags and target, so they don't step on each other. */
	instruction = 0x40000000 | (flags & 0x3FF0003) | (offset & 0xFFFC);

	return instruction;
}

static inline unsigned int branch_opcode(unsigned int instr)
{
	return (instr >> 26) & 0x3F;
}

static inline int instr_is_branch_iform(unsigned int instr)
{
	return branch_opcode(instr) == 18;
}

static inline int instr_is_branch_bform(unsigned int instr)
{
	return branch_opcode(instr) == 16;
}

static inline unsigned long branch_iform_target(const unsigned int instr)
{
	signed long imm;

	imm = instr & 0x3FFFFFC;

	/* If the top bit of the immediate value is set this is negative */
	if (imm & 0x2000000)
		imm -= 0x4000000;

	return (unsigned long)imm;
}

static inline unsigned long branch_bform_target(const unsigned int instr)
{
	signed long imm;

	imm = instr & 0xFFFC;

	/* If the top bit of the immediate value is set this is negative */
	if (imm & 0x8000)
		imm -= 0x10000;

	return (unsigned long)imm;
}

static inline int has_branch_target(const unsigned int instr)
{
	if (instr_is_branch_iform(instr))
		return 1;
	else if (instr_is_branch_bform(instr))
		return 1;

	return 0;
}

static inline int is_branch_absolute(const unsigned int instr)
{
	if (instr & BRANCH_ABSOLUTE)
		return 1;
	return 0;
}

static inline uint64_t branch_target(const unsigned int instr, unsigned long pc)
{
	if (has_branch_target(instr)) {
		unsigned long addr;
		if (instr_is_branch_iform(instr))
			addr = branch_iform_target(instr);
		else /* if (instr_is_branch_bform(instr)) */
			addr = branch_bform_target(instr);
		if (!is_branch_absolute(pc))
			addr += pc;
		return addr;
	}

	return 0;
}

static inline unsigned int set_branch_target(unsigned int insn, unsigned long iaddr, unsigned long btarget)
{
	if (instr_is_branch_iform(insn))
		return create_branch(iaddr, btarget, insn);
	else if (instr_is_branch_bform(insn))
		return create_cond_branch(iaddr, btarget, insn);
	else
		return insn;
}

#endif
