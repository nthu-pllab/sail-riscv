union clause ast = PEXT_P11 : (regidx, regidx, regidx, p_p11)

mapping clause encdec = PEXT_P11(rs1, rs2, rd, MVM) <->
  0b1 @ 0b0101 @ 0b00 @ rs2 @ rs1 @ 0b001 @ rd @ 0b0111011
mapping clause encdec = PEXT_P11(rs1, rs2, rd, MVMN) <->
  0b1 @ 0b0101 @ 0b01 @ rs2 @ rs1 @ 0b001 @ rd @ 0b0111011
mapping clause encdec = PEXT_P11(rs1, rs2, rd, MERGE) <->
  0b1 @ 0b0101 @ 0b10 @ rs2 @ rs1 @ 0b001 @ rd @ 0b0111011
mapping clause encdec = PEXT_P11(rs1, rs2, rd, SRX) <->
  0b1 @ 0b0101 @ 0b11 @ rs2 @ rs1 @ 0b001 @ rd @ 0b0111011
mapping clause encdec = PEXT_P11(rs1, rs2, rd, PDIFSUMU_B) <->
  0b1 @ 0b0110 @ 0b10 @ rs2 @ rs1 @ 0b001 @ rd @ 0b0111011
mapping clause encdec = PEXT_P11(rs1, rs2, rd, PDIFSUMAU_B) <->
  0b1 @ 0b0111 @ 0b10 @ rs2 @ rs1 @ 0b001 @ rd @ 0b0111011
mapping clause encdec = PEXT_P11(rs1, rs2, rd, PMUL_H_B01) <->
  0b1 @ 0b0010 @ 0b00 @ rs2 @ rs1 @ 0b001 @ rd @ 0b0111011
mapping clause encdec = PEXT_P11(rs1, rs2, rd, PMULU_H_B01) <->
  0b1 @ 0b0110 @ 0b00 @ rs2 @ rs1 @ 0b001 @ rd @ 0b0111011
mapping clause encdec = PEXT_P11(rs1, rs2, rd, MUL_H01) if sizeof(xlen) == 32 <->
  0b1 @ 0b0010 @ 0b01 @ rs2 @ rs1 @ 0b001 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_P11(rs1, rs2, rd, MACC_H01) if sizeof(xlen) == 32 <->
  0b1 @ 0b0011 @ 0b01 @ rs2 @ rs1 @ 0b001 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_P11(rs1, rs2, rd, MULU_H01) if sizeof(xlen) == 32 <->
  0b1 @ 0b0110 @ 0b01 @ rs2 @ rs1 @ 0b001 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_P11(rs1, rs2, rd, MACCU_H01) if sizeof(xlen) == 32 <->
  0b1 @ 0b0111 @ 0b01 @ rs2 @ rs1 @ 0b001 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_P11(rs1, rs2, rd, PMUL_W_H01) if sizeof(xlen) == 64 <->
  0b1 @ 0b0010 @ 0b01 @ rs2 @ rs1 @ 0b001 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_P11(rs1, rs2, rd, PMACC_W_H01) if sizeof(xlen) == 64 <->
  0b1 @ 0b0011 @ 0b01 @ rs2 @ rs1 @ 0b001 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_P11(rs1, rs2, rd, PMULU_W_H01) if sizeof(xlen) == 64 <->
  0b1 @ 0b0110 @ 0b01 @ rs2 @ rs1 @ 0b001 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_P11(rs1, rs2, rd, PMACCU_W_H01) if sizeof(xlen) == 64 <->
  0b1 @ 0b0111 @ 0b01 @ rs2 @ rs1 @ 0b001 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_P11(rs1, rs2, rd, MUL_W01) if sizeof(xlen) == 64 <->
  0b1 @ 0b0010 @ 0b11 @ rs2 @ rs1 @ 0b001 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_P11(rs1, rs2, rd, MACC_W01) if sizeof(xlen) == 64 <->
  0b1 @ 0b0011 @ 0b11 @ rs2 @ rs1 @ 0b001 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_P11(rs1, rs2, rd, MULU_W01) if sizeof(xlen) == 64 <->
  0b1 @ 0b0110 @ 0b11 @ rs2 @ rs1 @ 0b001 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_P11(rs1, rs2, rd, MACCU_W01) if sizeof(xlen) == 64 <->
  0b1 @ 0b0111 @ 0b11 @ rs2 @ rs1 @ 0b001 @ rd @ 0b0111011 if sizeof(xlen) == 64

function clause execute (PEXT_P11(rs1, rs2, rd, op)) = {
  match op {
    // TODO: I don't understand the 4 scalar instructions so please check it.
    MVM => {
      let s2 = X(rs2);
      X(rd) = (not_vec(s2) & X(rd)) | (s2 & X(rs1));
    },
    MVMN => {
      let s2 = X(rs2);
      X(rd) = (not_vec(s2) & X(rs1)) | (s2 & X(rd));
    },
    MERGE => {
      let d = X(rd);
      X(rd) = (not_vec(d) & X(rs1)) | (d & X(rs2));
    },
    SRX => {
      let shamt : bits(8) = match sizeof(xlen) {
        32 => EXTZ(X(rs2)[4..0]),
        64 => EXTZ(X(rs2)[5..0]),
        _ => return RETIRE_FAIL
      };
      X(rd) = ((X(rs1) @ X(rd)) >> shamt)[(sizeof(xlen) - 1)..0];
    },
    PDIFSUMU_B => {
      let s1 = X(rs1);
      let s2 = X(rs2);
      var sum : bits(xlen) = zeros();
      foreach (i from 0 to (sizeof(xlen) - 8) by 8) {
        let rs1_byte : bits(xlen) = EXTZ(s1[(i+7)..i]);
        let rs2_byte : bits(xlen) = EXTZ(s2[(i+7)..i]);
        sum = sum + abs(rs1_byte - rs2_byte);
      };
      X(rd) = sum;
    },
    PDIFSUMAU_B => {
      let s1 = X(rs1);
      let s2 = X(rs2);
      var sum : bits(xlen) = zeros();
      foreach (i from 0 to (sizeof(xlen) - 8) by 8) {
        let rs1_byte : bits(xlen) = EXTZ(s1[(i+7)..i]);
        let rs2_byte : bits(xlen) = EXTZ(s2[(i+7)..i]);
        sum = sum + abs(rs1_byte - rs2_byte);
      };
      X(rd) = X(rd) + sum;
    },
    PMUL_H_B01 => {
      let s1 = X(rs1);
      let s2 = X(rs2);
      var result : xlenbits = zeros();
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        let rs1_byte = signed(s1[(i+7)..i]);
        let rs2_byte = signed(s2[(i+15)..(i+8)]);
        result[(i+15)..i] = to_bits(16, rs1_byte * rs2_byte);
      };
      X(rd) = result;
    },
    PMULU_H_B01 => {
      let s1 = X(rs1);
      let s2 = X(rs2);
      var result : xlenbits = zeros();
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        let rs1_byte = unsigned(s1[(i+7)..i]);
        let rs2_byte = unsigned(s2[(i+15)..(i+8)]);
        result[(i+15)..i] = to_bits(16, rs1_byte * rs2_byte);
      };
      X(rd) = result;
    },
    MUL_H01 => {
      let s1 = X(rs1);
      let s2 = X(rs2);
      let rs1_halfword = signed(s1[15..0]);
      let rs2_halfword = signed(s2[31..16]);
      X(rd) = to_bits(sizeof(xlen), rs1_halfword * rs2_halfword);
    },
    MACC_H01 => {
      let s1 = X(rs1);
      let s2 = X(rs2);
      let rs1_halfword = signed(s1[15..0]);
      let rs2_halfword = signed(s2[31..16]);
      X(rd) = X(rd) + to_bits(sizeof(xlen), rs1_halfword * rs2_halfword);
    },
    MULU_H01 => {
      let s1 = X(rs1);
      let s2 = X(rs2);
      let rs1_halfword = unsigned(s1[15..0]);
      let rs2_halfword = unsigned(s2[31..16]);
      X(rd) = to_bits(sizeof(xlen), rs1_halfword * rs2_halfword);
    },
    MACCU_H01 => {
      let s1 = X(rs1);
      let s2 = X(rs2);
      let rs1_halfword = unsigned(s1[15..0]);
      let rs2_halfword = unsigned(s2[31..16]);
      X(rd) = X(rd) + to_bits(sizeof(xlen), rs1_halfword * rs2_halfword);
    },
    PMUL_W_H01 => {
      let s1 = X(rs1);
      let s2 = X(rs2);
      var result : xlenbits = zeros();
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        let rs1_byte = signed(s1[(i+15)..i]);
        let rs2_byte = signed(s2[(i+31)..(i+16)]);
        result[(i+31)..i] = to_bits(32, rs1_byte * rs2_byte);
      };
      X(rd) = result;
    },
    PMACC_W_H01 => {
      let s1 = X(rs1);
      let s2 = X(rs2);
      var result : xlenbits = zeros();
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        let rs1_byte = signed(s1[(i+15)..i]);
        let rs2_byte = signed(s2[(i+31)..(i+16)]);
        result[(i+31)..i] = X(rd)[(i+31)..i] + to_bits(32, rs1_byte * rs2_byte);
      };
      X(rd) = result;
    },
    PMULU_W_H01 => {
      let s1 = X(rs1);
      let s2 = X(rs2);
      var result : xlenbits = zeros();
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        let rs1_byte = unsigned(s1[(i+15)..i]);
        let rs2_byte = unsigned(s2[(i+31)..(i+16)]);
        result[(i+31)..i] = to_bits(32, rs1_byte * rs2_byte);
      };
      X(rd) = result;
    },
    PMACCU_W_H01 => {
      let s1 = X(rs1);
      let s2 = X(rs2);
      var result : xlenbits = zeros();
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        let rs1_byte = unsigned(s1[(i+15)..i]);
        let rs2_byte = unsigned(s2[(i+31)..(i+16)]);
        result[(i+31)..i] = X(rd)[(i+31)..i] + to_bits(32, rs1_byte * rs2_byte);
      };
      X(rd) = result;
    },
    MUL_W01 if sizeof(xlen) == 64 => {
      let s1 = X(rs1);
      let s2 = X(rs2);
      let rs1_word = signed(s1[31..0]);
      let rs2_word = signed(s2[63..32]);
      X(rd) = to_bits(sizeof(xlen), rs1_word * rs2_word);
    },
    MACC_W01 if sizeof(xlen) == 64 => {
      let s1 = X(rs1);
      let s2 = X(rs2);
      let rs1_word = signed(s1[31..0]);
      let rs2_word = signed(s2[63..32]);
      X(rd) = X(rd) + to_bits(sizeof(xlen), rs1_word * rs2_word);
    },
    MULU_W01 if sizeof(xlen) == 64 => {
      let s1 = X(rs1);
      let s2 = X(rs2);
      let rs1_word = unsigned(s1[31..0]);
      let rs2_word = unsigned(s2[63..32]);
      X(rd) = to_bits(sizeof(xlen), rs1_word * rs2_word);
    },
    MACCU_W01 if sizeof(xlen) == 64 => {
      let s1 = X(rs1);
      let s2 = X(rs2);
      let rs1_word = unsigned(s1[31..0]);
      let rs2_word = unsigned(s2[63..32]);
      X(rd) = X(rd) + to_bits(sizeof(xlen), rs1_word * rs2_word);
    },
    MUL_W01 => {
      return RETIRE_FAIL; // TODO: In order to please the coverage checker.
    },
    MACC_W01 => {
      return RETIRE_FAIL; // TODO: In order to please the coverage checker.
    },
    MULU_W01 => {
      return RETIRE_FAIL; // TODO: In order to please the coverage checker.
    },
    MACCU_W01 => {
      return RETIRE_FAIL; // TODO: In order to please the coverage checker.
    }
  };
  RETIRE_SUCCESS
}

mapping p_p11_mapping : p_p11 <-> string = {
  MVM <-> "mvm",
  MVMN <-> "mvmn",
  MERGE <-> "merge",
  SRX <-> "srx",
  PDIFSUMU_B <-> "pdifsumu.b",
  PDIFSUMAU_B <-> "pdifsumau.b",
  PMUL_H_B01 <-> "pmul.h.b01",
  PMULU_H_B01 <-> "pmulu.h.b01",
  MUL_H01 <-> "mul.h01",
  MACC_H01 <-> "macc.h01",
  MULU_H01 <-> "mulu.h01",
  MACCU_H01 <-> "maccu.h01",
  PMUL_W_H01 <-> "pmul.w.h01",
  PMACC_W_H01 <-> "pmacc.w.h01",
  PMULU_W_H01 <-> "pmulu.w.h01",
  PMACCU_W_H01 <-> "pmaccu.w.h01",
  MUL_W01 <-> "mul.w01",
  MACC_W01 <-> "macc.w01",
  MULU_W01 <-> "mulu.w01",
  MACCU_W01 <-> "maccu.w01"
}

mapping clause assembly = PEXT_P11(rs1, rs2, rd, p_inst)
  <-> p_p11_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2) // TODO: The order is probably correct, but we still have to check.
