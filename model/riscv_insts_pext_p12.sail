union clause ast = PEXT_SH1ADD : (regidx, regidx, regidx, p_sh1add)

mapping clause encdec = PEXT_SH1ADD(rs1, rs2, rd, PSH1ADD_H) <->
  0b1 @ 0b010 @ 0b0 @ 0b00 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0111011
mapping clause encdec = PEXT_SH1ADD(rs1, rs2, rd, PSSH1SADD_H) <->
  0b1 @ 0b011 @ 0b0 @ 0b00 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0111011
mapping clause encdec = PEXT_SH1ADD(rs1, rs2, rd, SSH1SADD) if sizeof(xlen) == 32 <->
  0b1 @ 0b011 @ 0b0 @ 0b01 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_SH1ADD(rs1, rs2, rd, PSH1ADD_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b010 @ 0b0 @ 0b01 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_SH1ADD(rs1, rs2, rd, PSSH1SADD_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b011 @ 0b0 @ 0b01 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0111011 if sizeof(xlen) == 64

function clause execute (PEXT_SH1ADD(rs1, rs2, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  var result : xlenbits = zeros();
  match op {
    PSH1ADD_H => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        result[(i+15)..i] = shift_left_logic(rs1_val[(i+15)..i], 0x01) + rs2_val[(i+15)..i];
      };
    },
    PSSH1SADD_H => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        result[(i+15)..i] = sadd(sat_shift_left_arith(rs1_val[(i+15)..i], 0x01), rs2_val[(i+15)..i]);
      };
    },
    SSH1SADD => {
      result = sadd(sat_shift_left_arith(rs1_val, 0x01), rs2_val);
    },
    PSH1ADD_W => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        result[(i+31)..i] = shift_left_logic(rs1_val[(i+31)..i], 0x01) + rs2_val[(i+31)..i];
      };
    },
    PSSH1SADD_W => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        result[(i+31)..i] = sadd(sat_shift_left_arith(rs1_val[(i+31)..i], 0x01), rs2_val[(i+31)..i]);
      };
    },
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_sh1add_mapping : p_sh1add <-> string = {
  PSH1ADD_H <-> "psh1add.h",
  PSSH1SADD_H <-> "pssh1sadd.h",
  SSH1SADD <-> "ssh1sadd",
  PSH1ADD_W <-> "psh1add.w",
  PSSH1SADD_W <-> "pssh1sadd.w"
}

mapping clause assembly = PEXT_SH1ADD(rs1, rs2, rd, p_inst)
  <-> p_sh1add_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)
