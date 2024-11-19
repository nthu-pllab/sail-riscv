union clause ast = PEXT_ADD_SHIFT : (regidx, regidx, regidx, p_add_shift)

mapping clause encdec = PEXT_ADD_SHIFT(rs1, rs2, rd, PSLL_B_B0) <->
  0b1 @ 0b000 @ 0b1 @ 0b10 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0011011
mapping clause encdec = PEXT_ADD_SHIFT(rs1, rs2, rd, PADD_B_B0) <->
  0b1 @ 0b001 @ 0b1 @ 0b10 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0011011
mapping clause encdec = PEXT_ADD_SHIFT(rs1, rs2, rd, PSLL_H_H0) <->
  0b1 @ 0b000 @ 0b1 @ 0b00 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0011011
mapping clause encdec = PEXT_ADD_SHIFT(rs1, rs2, rd, PADD_H_H0) <->
  0b1 @ 0b001 @ 0b1 @ 0b00 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0011011
mapping clause encdec = PEXT_ADD_SHIFT(rs1, rs2, rd, PSSHA_H_H0) <->
  0b1 @ 0b110 @ 0b1 @ 0b00 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0011011
mapping clause encdec = PEXT_ADD_SHIFT(rs1, rs2, rd, PSSHAR_H_H0) <->
  0b1 @ 0b111 @ 0b1 @ 0b00 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0011011
mapping clause encdec = PEXT_ADD_SHIFT(rs1, rs2, rd, PSLL_W_W0) if sizeof(xlen) == 64 <->
  0b1 @ 0b000 @ 0b1 @ 0b01 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0011011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_ADD_SHIFT(rs1, rs2, rd, PADD_W_W0) if sizeof(xlen) == 64 <->
  0b1 @ 0b001 @ 0b1 @ 0b01 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0011011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_ADD_SHIFT(rs1, rs2, rd, PSSHA_W_W0) if sizeof(xlen) == 64 <->
  0b1 @ 0b110 @ 0b1 @ 0b01 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0011011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_ADD_SHIFT(rs1, rs2, rd, PSSHAR_W_W0) if sizeof(xlen) == 64 <->
  0b1 @ 0b111 @ 0b1 @ 0b01 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0011011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_ADD_SHIFT(rs1, rs2, rd, SSHA) if sizeof(xlen) == 32 <->
  0b1 @ 0b110 @ 0b1 @ 0b01 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0011011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_ADD_SHIFT(rs1, rs2, rd, SSHAR) if sizeof(xlen) == 32 <->
  0b1 @ 0b111 @ 0b1 @ 0b01 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0011011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_ADD_SHIFT(rs1, rs2, rd, SHA) if sizeof(xlen) == 64 <->
  0b1 @ 0b110 @ 0b1 @ 0b11 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0011011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_ADD_SHIFT(rs1, rs2, rd, SHAR) if sizeof(xlen) == 64 <->
  0b1 @ 0b111 @ 0b1 @ 0b11 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0011011 if sizeof(xlen) == 64

function clause execute (PEXT_ADD_SHIFT(rs1, rs2, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  var result : xlenbits = zeros();
  match op {
    PSLL_B_B0 => {
      foreach (i from 0 to (sizeof(xlen) - 8) by 8) {
        result[(i+7)..i] = shift_left_logic(rs1_val[(i+7)..i], EXTZ(rs2_val[2..0]))
      };
    },
    PADD_B_B0 => {
      foreach (i from 0 to (sizeof(xlen) - 8) by 8) {
        result[(i+7)..i] = rs1_val[(i+7)..i] + rs2_val[(i+7)..i]
      };
    },
    PSLL_H_H0 => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        result[(i+15)..i] = shift_left_logic(rs1_val[(i+15)..i], EXTZ(rs2_val[3..0]))
      };
    },
    PADD_H_H0 => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        result[(i+15)..i] = rs1_val[(i+15)..i] + rs2_val[(i+15)..i]
      };
    },
    PSSHA_H_H0 => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        result[(i+15)..i] = ssha(rs1_val[(i+15)..i], EXTS(rs2_val[4..0]))
      };
    },
    PSSHAR_H_H0 => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        result[(i+15)..i] = sshar(rs1_val[(i+15)..i], EXTS(rs2_val[4..0]))
      };
    },
    PSLL_W_W0 => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        result[(i+31)..i] = shift_left_logic(rs1_val[(i+31)..i], EXTZ(rs2_val[4..0]))
      };
    },
    PADD_W_W0 => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        result[(i+31)..i] = rs1_val[(i+31)..i] + rs2_val[(i+31)..i]
      };
    },
    PSSHA_W_W0 => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        result[(i+31)..i] = ssha(rs1_val[(i+31)..i], EXTS(rs2_val[5..0]))
      };
    },
    PSSHAR_W_W0 => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        result[(i+31)..i] = sshar(rs1_val[(i+31)..i], EXTS(rs2_val[5..0]))
      };
    },
    SSHA => result = ssha(rs1_val, EXTS(rs2_val[5..0])),
    SSHAR => result = sshar(rs1_val, EXTS(rs2_val[5..0])),
    SHA => result = sha(rs1_val, EXTS(rs2_val[5..0])),
    SHAR => result = shar(rs1_val, EXTS(rs2_val[5..0]))
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_add_shift_mapping : p_add_shift <-> string = {
  PSLL_B_B0 <-> "psll.b.b0",
  PADD_B_B0 <-> "padd.b.b0",
  PSLL_H_H0 <-> "psll.h.h0",
  PADD_H_H0 <-> "padd.h.h0",
  PSSHA_H_H0 <-> "pssha.h.h0",
  PSSHAR_H_H0 <-> "psshar.h.h0",
  PSLL_W_W0 <-> "psll.w.w0",
  PADD_W_W0 <-> "padd.w.w0",
  PSSHA_W_W0 <-> "pssha.w.w0",
  PSSHAR_W_W0 <-> "psshar.w.w0",
  SSHA <-> "ssha",
  SSHAR <-> "sshar",
  SHA <-> "sha",
  SHAR <-> "shar"
}

mapping clause assembly = PEXT_ADD_SHIFT(rs1, rs2, rd, p_inst)
  <-> p_add_shift_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2) // TODO: The order is probably correct, but we still have to check.
  