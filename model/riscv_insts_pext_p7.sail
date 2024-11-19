union clause ast = PEXT_PS : (regidx, regidx, p_ps)

mapping clause encdec = PEXT_PS(rs1, rd, PSABS_B) <->
  0b11100 @ 0b10 @ 0b00111 @ rs1 @ 0b010 @ rd @ 0b0011011
mapping clause encdec = PEXT_PS(rs1, rd, PSABS_H) <->
  0b11100 @ 0b00 @ 0b00111 @ rs1 @ 0b010 @ rd @ 0b0011011
mapping clause encdec = PEXT_PS(rs1, rd, PSEXTB_H) <->
  0b11100 @ 0b00 @ 0b00100 @ rs1 @ 0b010 @ rd @ 0b0011011
mapping clause encdec = PEXT_PS(rs1, rd, PSEXTB_W) if sizeof(xlen) == 64 <->
  0b11100 @ 0b01 @ 0b00100 @ rs1 @ 0b010 @ rd @ 0b0011011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_PS(rs1, rd, PSEXTH_W) if sizeof(xlen) == 64 <->
  0b11100 @ 0b01 @ 0b00101 @ rs1 @ 0b010 @ rd @ 0b0011011 if sizeof(xlen) == 64

function clause execute (PEXT_PS(rs1, rd, op)) = { // TODO: Double check if this is correct.
  let rs1_val = X(rs1);
  var result : xlenbits = zeros();
  match op {
    PSABS_B => {
      foreach (i from 0 to (sizeof(xlen) - 8) by 8) {
        let rs1_byte = slice(rs1_val, i, 8);
        result[(i+7)..i] = sabs(rs1_byte)
      };
    },
    PSABS_H => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        let rs1_halfword = slice(rs1_val, i, 16);
        result[(i+15)..i] = sabs(rs1_halfword)
      };
    },
    PSEXTB_H => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        result[(i+15)..i] = EXTS(rs1_val[7..0])
      };  
    },
    PSEXTB_W => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        result[(i+31)..i] = EXTS(rs1_val[7..0])
      };  
    },
    PSEXTH_W => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        result[(i+31)..i] = EXTS(rs1_val[15..0])
      };  
    }
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_ps_mapping : p_ps <-> string = {
  PSABS_B <-> "psabs.b",
  PSABS_H <-> "psabs.h",
  PSEXTB_H <-> "psextb.h",
  PSEXTB_W <-> "psextb.w",
  PSEXTH_W <-> "psexth.w"
}

mapping clause assembly = PEXT_PS(rs1, rd, p_inst)
  <-> p_ps_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)