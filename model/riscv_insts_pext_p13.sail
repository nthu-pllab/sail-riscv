union clause ast = PEXT_MUL_B : (regidx, regidx, regidx, p_mul_b)

mapping clause encdec = PEXT_MUL_B(rs1, rs2, rd, PMUL_H_B00) <->
  0b1 @ 0b0000 @ 0b00 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL_B(rs1, rs2, rd, PMUL_H_B11) <->
  0b1 @ 0b0010 @ 0b00 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL_B(rs1, rs2, rd, PMULU_H_B00) <->
  0b1 @ 0b0100 @ 0b00 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL_B(rs1, rs2, rd, PMULU_H_B11) <->
  0b1 @ 0b0110 @ 0b00 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL_B(rs1, rs2, rd, PMULSU_H_B00) <->
  0b1 @ 0b1100 @ 0b00 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL_B(rs1, rs2, rd, PMULSU_H_B11) <->
  0b1 @ 0b1110 @ 0b00 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011

function clause execute (PEXT_MUL_B(rs1, rs2, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  var result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
    let rs1_byte_even = slice(rs1_val, i, 8);
    let rs2_byte_even = slice(rs2_val, i, 8);
    let rs1_byte_odd = slice(rs1_val, i + 8, 8);
    let rs2_byte_odd = slice(rs2_val, i + 8, 8);
    result[(i+15)..i] = match op {
      PMUL_H_B00 => muls(rs1_byte_even, rs2_byte_even),
      PMUL_H_B11 => muls(rs1_byte_odd, rs2_byte_odd),
      PMULU_H_B00 => mulu(rs1_byte_even, rs2_byte_even),
      PMULU_H_B11 => mulu(rs1_byte_odd, rs2_byte_odd),
      PMULSU_H_B00 => mulsu(rs1_byte_even, rs2_byte_even),
      PMULSU_H_B11 => mulsu(rs1_byte_odd, rs2_byte_odd)
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_mul_b_mapping : p_mul_b <-> string = {
  PMUL_H_B00 <-> "pmul.h.b00",
  PMUL_H_B11 <-> "pmul.h.b11",
  PMULU_H_B00 <-> "pmulu.h.b00",
  PMULU_H_B11 <-> "pmulu.h.b11",
  PMULSU_H_B00 <-> "pmulsu.h.b00",
  PMULSU_H_B11 <-> "pmulsu.h.b11"
}

mapping clause assembly = PEXT_MUL_B(rs1, rs2, rd, p_inst)
  <-> p_mul_b_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/* ****************************************************************** */

union clause ast = PEXT_MUL_H : (regidx, regidx, regidx, p_mul_h)

mapping clause encdec = PEXT_MUL_H(rs1, rs2, rd, PMUL_W_H00) if sizeof(xlen) == 64 <->
  0b1 @ 0b0000 @ 0b01 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL_H(rs1, rs2, rd, PMUL_W_H11) if sizeof(xlen) == 64 <->
  0b1 @ 0b0010 @ 0b01 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL_H(rs1, rs2, rd, PMULU_W_H00) if sizeof(xlen) == 64 <->
  0b1 @ 0b0100 @ 0b01 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL_H(rs1, rs2, rd, PMULU_W_H11) if sizeof(xlen) == 64 <->
  0b1 @ 0b0110 @ 0b01 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL_H(rs1, rs2, rd, PMULSU_W_H00) if sizeof(xlen) == 64 <->
  0b1 @ 0b1100 @ 0b01 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL_H(rs1, rs2, rd, PMULSU_W_H11) if sizeof(xlen) == 64 <->
  0b1 @ 0b1110 @ 0b01 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL_H(rs1, rs2, rd, PMACC_W_H00) if sizeof(xlen) == 64 <->
  0b1 @ 0b0001 @ 0b01 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL_H(rs1, rs2, rd, PMACC_W_H11) if sizeof(xlen) == 64 <->
  0b1 @ 0b0011 @ 0b01 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL_H(rs1, rs2, rd, PMACCU_W_H00) if sizeof(xlen) == 64 <->
  0b1 @ 0b0101 @ 0b01 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL_H(rs1, rs2, rd, PMACCU_W_H11) if sizeof(xlen) == 64 <->
  0b1 @ 0b0111 @ 0b01 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL_H(rs1, rs2, rd, PMACCSU_W_H00) if sizeof(xlen) == 64 <->
  0b1 @ 0b1101 @ 0b01 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL_H(rs1, rs2, rd, PMACCSU_W_H11) if sizeof(xlen) == 64 <->
  0b1 @ 0b1111 @ 0b01 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL_H(rs1, rs2, rd, PMQACC_W_H01) if sizeof(xlen) == 64 <->
  0b1 @ 0b1111 @ 0b00 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL_H(rs1, rs2, rd, PMQRACC_W_H01) if sizeof(xlen) == 64 <->
  0b1 @ 0b1111 @ 0b10 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL_H(rs1, rs2, rd, MUL_H00) if sizeof(xlen) == 32 <->
  0b1 @ 0b0000 @ 0b01 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_MUL_H(rs1, rs2, rd, MUL_H11) if sizeof(xlen) == 32 <->
  0b1 @ 0b0010 @ 0b01 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_MUL_H(rs1, rs2, rd, MULU_H00) if sizeof(xlen) == 32 <->
  0b1 @ 0b0100 @ 0b01 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_MUL_H(rs1, rs2, rd, MULU_H11) if sizeof(xlen) == 32 <->
  0b1 @ 0b0110 @ 0b01 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_MUL_H(rs1, rs2, rd, MULSU_H00) if sizeof(xlen) == 32 <->
  0b1 @ 0b1100 @ 0b01 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_MUL_H(rs1, rs2, rd, MULSU_H11) if sizeof(xlen) == 32 <->
  0b1 @ 0b1110 @ 0b01 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_MUL_H(rs1, rs2, rd, MACC_H00) if sizeof(xlen) == 32 <->
  0b1 @ 0b0001 @ 0b01 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_MUL_H(rs1, rs2, rd, MACC_H11) if sizeof(xlen) == 32 <->
  0b1 @ 0b0011 @ 0b01 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_MUL_H(rs1, rs2, rd, MACCU_H00) if sizeof(xlen) == 32 <->
  0b1 @ 0b0101 @ 0b01 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_MUL_H(rs1, rs2, rd, MACCU_H11) if sizeof(xlen) == 32 <->
  0b1 @ 0b0111 @ 0b01 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_MUL_H(rs1, rs2, rd, MACCSU_H00) if sizeof(xlen) == 32 <->
  0b1 @ 0b1101 @ 0b01 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_MUL_H(rs1, rs2, rd, MACCSU_H11) if sizeof(xlen) == 32 <->
  0b1 @ 0b1111 @ 0b01 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_MUL_H(rs1, rs2, rd, MQACC_H01) if sizeof(xlen) == 32 <->
  0b1 @ 0b1111 @ 0b00 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_MUL_H(rs1, rs2, rd, MQRACC_H01) if sizeof(xlen) == 32 <->
  0b1 @ 0b1111 @ 0b10 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011 if sizeof(xlen) == 32

function clause execute (PEXT_MUL_H(rs1, rs2, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  let rd_val = X(rd);
  var result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
    let rs1_halfword_even = slice(rs1_val, i, 16);
    let rs2_halfword_even = slice(rs2_val, i, 16);
    let rs1_halfword_odd = slice(rs1_val, i + 16, 16);
    let rs2_halfword_odd = slice(rs2_val, i + 16, 16);
    result[(i+31)..i] = match op {
      PMUL_W_H00 => muls(rs1_halfword_even, rs2_halfword_even),
      PMUL_W_H11 => muls(rs1_halfword_odd, rs2_halfword_odd),
      PMULU_W_H00 => mulu(rs1_halfword_even, rs2_halfword_even),
      PMULU_W_H11 => mulu(rs1_halfword_odd, rs2_halfword_odd),
      PMULSU_W_H00 => mulsu(rs1_halfword_even, rs2_halfword_even),
      PMULSU_W_H11 => mulsu(rs1_halfword_odd, rs2_halfword_odd),
      PMACC_W_H00 => rd_val[(i+31)..i] + muls(rs1_halfword_even, rs2_halfword_even),
      PMACC_W_H11 => rd_val[(i+31)..i] + muls(rs1_halfword_odd, rs2_halfword_odd),
      PMACCU_W_H00 => rd_val[(i+31)..i] + mulu(rs1_halfword_even, rs2_halfword_even),
      PMACCU_W_H11 => rd_val[(i+31)..i] + mulu(rs1_halfword_odd, rs2_halfword_odd),
      PMACCSU_W_H00 => rd_val[(i+31)..i] + mulsu(rs1_halfword_even, rs2_halfword_even),
      PMACCSU_W_H11 => rd_val[(i+31)..i] + mulsu(rs1_halfword_odd, rs2_halfword_odd),
      PMQRACC_W_H01 => rd_val[(i+31)..i] + mulqr(rs1_halfword_even, rs2_halfword_odd),
      PMQACC_W_H01 => rd_val[(i+31)..i] + mulq(rs1_halfword_even, rs2_halfword_odd),
      MUL_H00 => muls(rs1_halfword_even, rs2_halfword_even),
      MUL_H11 => muls(rs1_halfword_odd, rs2_halfword_odd),
      MULU_H00 => mulu(rs1_halfword_even, rs2_halfword_even),
      MULU_H11 => mulu(rs1_halfword_odd, rs2_halfword_odd),
      MULSU_H00 => mulsu(rs1_halfword_even, rs2_halfword_even),
      MULSU_H11 => mulsu(rs1_halfword_odd, rs2_halfword_odd),
      MACC_H00 => rd_val[(i+31)..i] + muls(rs1_halfword_even, rs2_halfword_even),
      MACC_H11 => rd_val[(i+31)..i] + muls(rs1_halfword_odd, rs2_halfword_odd),
      MACCU_H00 => rd_val[(i+31)..i] + mulu(rs1_halfword_even, rs2_halfword_even),
      MACCU_H11 => rd_val[(i+31)..i] + mulu(rs1_halfword_odd, rs2_halfword_odd),
      MACCSU_H00 => rd_val[(i+31)..i] + mulsu(rs1_halfword_even, rs2_halfword_even),
      MACCSU_H11 => rd_val[(i+31)..i] + mulsu(rs1_halfword_odd, rs2_halfword_odd),
      MQRACC_H01 => rd_val[(i+31)..i] + mulqr(rs1_halfword_even, rs2_halfword_odd),
      MQACC_H01 => rd_val[(i+31)..i] + mulq(rs1_halfword_even, rs2_halfword_odd)
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_mul_h_mapping : p_mul_h <-> string = {
  PMUL_W_H00 <-> "pmul.w.h00",
  PMUL_W_H11 <-> "pmul.w.h11",
  PMULU_W_H00 <-> "pmulu.w.h00",
  PMULU_W_H11 <-> "pmulu.w.h11",
  PMULSU_W_H00 <-> "pmulsu.w.h00",
  PMULSU_W_H11 <-> "pmulsu.w.h11",
  PMACC_W_H00 <-> "pmacc.w.h00",
  PMACC_W_H11 <-> "pmacc.w.h11",
  PMACCU_W_H00 <-> "pmaccu.w.h00",
  PMACCU_W_H11 <-> "pmaccu.w.h11",
  PMACCSU_W_H00 <-> "pmaccsu.w.h00",
  PMACCSU_W_H11 <-> "pmaccsu.w.h11",
  PMQRACC_W_H01 <-> "pmqracc.w.h01",
  PMQACC_W_H01 <-> "pmqacc.w.h01",
  MUL_H00 <-> "mul.h00",
  MUL_H11 <-> "mul.h11",
  MULU_H00 <-> "mulu.h00",
  MULU_H11 <-> "mulu.h11",
  MULSU_H00 <-> "mulsu.h00",
  MULSU_H11 <-> "mulsu.h11",
  MACC_H00 <-> "macc.h00",
  MACC_H11 <-> "macc.h11",
  MACCU_H00 <-> "maccu.h00",
  MACCU_H11 <-> "maccu.h11",
  MACCSU_H00 <-> "maccsu.h00",
  MACCSU_H11 <-> "maccsu.h11",
  MQRACC_H01 <-> "mqracc.h01",
  MQACC_H01 <-> "mqacc.h01"
}

mapping clause assembly = PEXT_MUL_H(rs1, rs2, rd, p_inst)
  <-> p_mul_h_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)
