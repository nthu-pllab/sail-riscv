union clause ast = PEXT_MUL : (regidx, regidx, regidx, p_mul)

mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMULH_H) <->
  0b1 @ 0b0000 @ 0b00 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMHACC_H) <->
  0b1 @ 0b0001 @ 0b00 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMULHU_H) <->
  0b1 @ 0b0010 @ 0b00 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMHACCU_H) <->
  0b1 @ 0b0011 @ 0b00 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMULH_H_BE) <->
  0b1 @ 0b0100 @ 0b00 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMHACC_H_BE) <->
  0b1 @ 0b0101 @ 0b00 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMULH_H_BO) <->
  0b1 @ 0b0110 @ 0b00 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMHACC_H_BO) <->
  0b1 @ 0b0111 @ 0b00 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011
// TODO:
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMULHR_H) <->
  0b1 @ 0b0000 @ 0b10 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMHRACC_H) <->
  0b1 @ 0b0001 @ 0b10 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMULHRU_H) <->
  0b1 @ 0b0010 @ 0b10 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMHRACCU_H) <->
  0b1 @ 0b0011 @ 0b10 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011

function clause execute (PEXT_MUL(rs1, rs2, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  let rd_val = X(rd);
  var result : xlenbits = zeros();
  match op {
    PMULH_H => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        let rs1_halfword = rs1_val[(i+15)..i];
        let rs2_halfword = rs2_val[(i+15)..i];
        result[(i+15)..i] = mulh(rs1_halfword, rs2_halfword);
      }
    },
    PMHACC_H => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        let rs1_halfword = rs1_val[(i+15)..i];
        let rs2_halfword = rs2_val[(i+15)..i];
        let rd_halfword = rd_val[(i+15)..i];
        result[(i+15)..i] = rd_halfword + mulh(rs1_halfword, rs2_halfword);
      }
    },
    PMULHU_H => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        let rs1_halfword = rs1_val[(i+15)..i];
        let rs2_halfword = rs2_val[(i+15)..i];
        result[(i+15)..i] = mulhu(rs1_halfword, rs2_halfword);
      }
    },
    PMHACCU_H => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        let rs1_halfword = rs1_val[(i+15)..i];
        let rs2_halfword = rs2_val[(i+15)..i];
        let rd_halfword = rd_val[(i+15)..i];
        result[(i+15)..i] = rd_halfword + mulhu(rs1_halfword, rs2_halfword);
      }
    },
    PMULH_H_BE => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        let rs1_halfword = rs1_val[(i+15)..i];
        let rs2_halfword = EXTS(16, rs2_val[(i+7)..i]);
        result[(i+15)..i] = mulh(rs1_halfword, rs2_halfword);
      }
    },
    PMHACC_H_BE => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        let rs1_halfword = rs1_val[(i+15)..i];
        let rs2_halfword = EXTS(16, rs2_val[(i+7)..i]);
        let rd_halfword = rd_val[(i+15)..i];
        result[(i+15)..i] = rd_halfword + mulh(rs1_halfword, rs2_halfword);
      }
    },
    PMULH_H_BO => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        let rs1_halfword = rs1_val[(i+15)..i];
        let rs2_halfword = EXTS(16, rs2_val[(i+15)..(i+8)]);
        result[(i+15)..i] = mulh(rs1_halfword, rs2_halfword);
      }
    },
    PMHACC_H_BO => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        let rs1_halfword = rs1_val[(i+15)..i];
        let rs2_halfword = EXTS(16, rs2_val[(i+15)..(i+8)]);
        let rd_halfword = rd_val[(i+15)..i];
        result[(i+15)..i] = rd_halfword + mulh(rs1_halfword, rs2_halfword);
      }
    },
    PMULHR_H => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        let rs1_halfword = rs1_val[(i+15)..i];
        let rs2_halfword = rs2_val[(i+15)..i];
        result[(i+15)..i] = mulhr(rs1_halfword, rs2_halfword);
      }
    },
    PMHRACC_H => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        let rs1_halfword = rs1_val[(i+15)..i];
        let rs2_halfword = rs2_val[(i+15)..i];
        let rd_halfword = rd_val[(i+15)..i];
        result[(i+15)..i] = rd_halfword + mulhr(rs1_halfword, rs2_halfword);
      }
    },
    PMULHRU_H => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        let rs1_halfword = rs1_val[(i+15)..i];
        let rs2_halfword = rs2_val[(i+15)..i];
        result[(i+15)..i] = mulhru(rs1_halfword, rs2_halfword);
      }
    },
    PMHRACCU_H => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        let rs1_halfword = rs1_val[(i+15)..i];
        let rs2_halfword = rs2_val[(i+15)..i];
        let rd_halfword = rd_val[(i+15)..i];
        result[(i+15)..i] = rd_halfword + mulhru(rs1_halfword, rs2_halfword);
      }
    },
    PMULHSU_H_BE => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        let rs1_halfword = rs1_val[(i+15)..i];
        let rs2_halfword = EXTZ(16, rs2_val[(i+7)..i]);
        result[(i+15)..i] = mulhsu(rs1_halfword, rs2_halfword);
      }
    },
    PMHACCSU_H_BE => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        let rs1_halfword = rs1_val[(i+15)..i];
        let rs2_halfword = EXTZ(16, rs2_val[(i+7)..i]);
        let rd_halfword = rd_val[(i+15)..i];
        result[(i+15)..i] = rd_halfword + mulhu(rs1_halfword, rs2_halfword);
      }
    },
    PMULHSU_H_BO => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        let rs1_halfword = rs1_val[(i+15)..i];
        let rs2_halfword = EXTZ(16, rs2_val[(i+15)..(i+8)]);
        result[(i+15)..i] = mulhu(rs1_halfword, rs2_halfword);
      }
    },
    PMHACCSU_H_BO => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        let rs1_halfword = rs1_val[(i+15)..i];
        let rs2_halfword = EXTZ(16, rs2_val[(i+15)..(i+8)]);
        let rd_halfword = rd_val[(i+15)..i];
        result[(i+15)..i] = rd_halfword + mulhu(rs1_halfword, rs2_halfword);
      }
    }
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_mul_mapping : p_mul <-> string = {
  PMULH_H <-> "pmulh.h",
  PMHACC_H <-> "pmhacc.h",
  PMULHU_H <-> "pmulhu.h",
  PMHACCU_H <-> "pmhaccu.h",
  PMULH_H_BE <-> "pmulh.h.be",
  PMHACC_H_BE <-> "pmhacc.h.be",
  PMULH_H_BO <-> "pmulh.h.bo",
  PMHACC_H_BO <-> "pmhacc.h.bo",
  PMULHR_H <-> "pmulhr.h",
  PMHRACC_H <-> "pmhracc.h",
  PMULHRU_H <-> "pmulhru.h",
  PMHRACCU_H <-> "pmhraccu.h",
  PMULHSU_H_BE <-> "pmulhsu.h.be",
  PMHACCSU_H_BE <-> "pmhaccsu.h.be",
  PMULHSU_H_BO <-> "pmulhsu.h.bo",
  PMHACCSU_H_BO <-> "pmhaccsu.h.bo"
}

mapping clause assembly = PEXT_MUL(rs1, rs2, rd, p_inst)
  <-> p_mul_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

// TODO: To be continued ...
