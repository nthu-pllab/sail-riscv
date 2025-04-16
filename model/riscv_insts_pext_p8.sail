union clause ast = PEXT_ADD_SHIFT : (regidx, regidx, regidx, p_add_shift)

mapping clause encdec = PEXT_ADD_SHIFT(rs1, rs2, rd, PSLL_BS) <->
  0b1 @ 0b000 @ 0b1 @ 0b10 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0011011
mapping clause encdec = PEXT_ADD_SHIFT(rs1, rs2, rd, PADD_BS) <->
  0b1 @ 0b001 @ 0b1 @ 0b10 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0011011
mapping clause encdec = PEXT_ADD_SHIFT(rs1, rs2, rd, PSLL_HS) <->
  0b1 @ 0b000 @ 0b1 @ 0b00 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0011011
mapping clause encdec = PEXT_ADD_SHIFT(rs1, rs2, rd, PADD_HS) <->
  0b1 @ 0b001 @ 0b1 @ 0b00 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0011011
mapping clause encdec = PEXT_ADD_SHIFT(rs1, rs2, rd, PSSHA_HS) <->
  0b1 @ 0b110 @ 0b1 @ 0b00 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0011011
mapping clause encdec = PEXT_ADD_SHIFT(rs1, rs2, rd, PSSHAR_HS) <->
  0b1 @ 0b111 @ 0b1 @ 0b00 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0011011
mapping clause encdec = PEXT_ADD_SHIFT(rs1, rs2, rd, PSLL_WS) if sizeof(xlen) == 64 <->
  0b1 @ 0b000 @ 0b1 @ 0b01 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0011011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_ADD_SHIFT(rs1, rs2, rd, PADD_WS) if sizeof(xlen) == 64 <->
  0b1 @ 0b001 @ 0b1 @ 0b01 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0011011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_ADD_SHIFT(rs1, rs2, rd, PSSHA_WS) if sizeof(xlen) == 64 <->
  0b1 @ 0b110 @ 0b1 @ 0b01 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0011011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_ADD_SHIFT(rs1, rs2, rd, PSSHAR_WS) if sizeof(xlen) == 64 <->
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
    PSLL_BS => {
      foreach (i from 0 to (sizeof(xlen) - 8) by 8) {
        result[(i+7)..i] = shift_left_logic(rs1_val[(i+7)..i], EXTZ(rs2_val[2..0]))
      };
    },
    PADD_BS => {
      foreach (i from 0 to (sizeof(xlen) - 8) by 8) {
        result[(i+7)..i] = rs1_val[(i+7)..i] + rs2_val[7..0]
      };
    },
    PSLL_HS => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        result[(i+15)..i] = shift_left_logic(rs1_val[(i+15)..i], EXTZ(rs2_val[3..0]))
      };
    },
    PADD_HS => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        result[(i+15)..i] = rs1_val[(i+15)..i] + rs2_val[15..0]
      };
    },
    PSSHA_HS => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        result[(i+15)..i] = ssha(rs1_val[(i+15)..i], rs2_val[7..0])
      };
    },
    PSSHAR_HS => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        result[(i+15)..i] = sshar(rs1_val[(i+15)..i], rs2_val[7..0])
      };
    },
    PSLL_WS => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        result[(i+31)..i] = shift_left_logic(rs1_val[(i+31)..i], EXTZ(rs2_val[4..0]))
      };
    },
    PADD_WS => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        result[(i+31)..i] = rs1_val[(i+31)..i] + rs2_val[31..0]
      };
    },
    PSSHA_WS => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        result[(i+31)..i] = ssha(rs1_val[(i+31)..i], rs2_val[7..0])
      };
    },
    PSSHAR_WS => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        result[(i+31)..i] = sshar(rs1_val[(i+31)..i], rs2_val[7..0])
      };
    },
    SSHA => result = ssha(rs1_val, rs2_val[7..0]),
    SSHAR => result = sshar(rs1_val, rs2_val[7..0]),
    SHA => result = sha(rs1_val, rs2_val[7..0]),
    SHAR => result = shar(rs1_val, rs2_val[7..0])
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_add_shift_mapping : p_add_shift <-> string = {
  PSLL_BS <-> "psll.bs",
  PADD_BS <-> "padd.bs",
  PSLL_HS <-> "psll.hs",
  PADD_HS <-> "padd.hs",
  PSSHA_HS <-> "pssha.hs",
  PSSHAR_HS <-> "psshar.hs",
  PSLL_WS <-> "psll.ws",
  PADD_WS <-> "padd.ws",
  PSSHA_WS <-> "pssha.ws",
  PSSHAR_WS <-> "psshar.ws",
  SSHA <-> "ssha",
  SSHAR <-> "sshar",
  SHA <-> "sha",
  SHAR <-> "shar"
}

mapping clause assembly = PEXT_ADD_SHIFT(rs1, rs2, rd, p_inst)
  <-> p_add_shift_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2) // TODO: The order is probably correct, but we still have to check.
  