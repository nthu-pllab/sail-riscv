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
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMULHSU_H) <->
  0b1 @ 0b1000 @ 0b00 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMHACCSU_H) <->
  0b1 @ 0b1001 @ 0b00 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMULQ_H) <->
  0b1 @ 0b1010 @ 0b00 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, MQACC_H00) if sizeof(xlen) == 32 <->
  0b1 @ 0b1101 @ 0b00 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, MQACC_H11) if sizeof(xlen) == 32 <->
  0b1 @ 0b1111 @ 0b00 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMQACC_W_HEE) if sizeof(xlen) == 64 <->
  0b1 @ 0b1101 @ 0b00 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMQACC_W_HOO) if sizeof(xlen) == 64 <->
  0b1 @ 0b1111 @ 0b00 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMULHR_H) <->
  0b1 @ 0b0000 @ 0b10 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMHRACC_H) <->
  0b1 @ 0b0001 @ 0b10 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMULHRU_H) <->
  0b1 @ 0b0010 @ 0b10 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMHRACCU_H) <->
  0b1 @ 0b0011 @ 0b10 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMULHSU_H_BE) <->
  0b1 @ 0b0100 @ 0b10 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMHACCSU_H_BE) <->
  0b1 @ 0b0101 @ 0b10 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMULHSU_H_BO) <->
  0b1 @ 0b0110 @ 0b10 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMHACCSU_H_BO) <->
  0b1 @ 0b0111 @ 0b10 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMULHRSU_H) <->
  0b1 @ 0b1000 @ 0b10 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMHRACCSU_H) <->
  0b1 @ 0b1001 @ 0b10 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMULQR_H) <->
  0b1 @ 0b1010 @ 0b10 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, MQRACC_H00) if sizeof(xlen) == 32 <->
  0b1 @ 0b1101 @ 0b10 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, MQRACC_H11) if sizeof(xlen) == 32 <->
  0b1 @ 0b1111 @ 0b10 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMQRACC_W_HEE) if sizeof(xlen) == 64 <->
  0b1 @ 0b1101 @ 0b10 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMQRACC_W_HOO) if sizeof(xlen) == 64 <->
  0b1 @ 0b1111 @ 0b10 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, MHACC) if sizeof(xlen) == 32 <->
  0b1 @ 0b0001 @ 0b01 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, MHACCU) if sizeof(xlen) == 32 <->
  0b1 @ 0b0011 @ 0b01 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, MULH_H0) if sizeof(xlen) == 32 <->
  0b1 @ 0b0100 @ 0b01 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, MHACC_H0) if sizeof(xlen) == 32 <->
  0b1 @ 0b0101 @ 0b01 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, MULH_H1) if sizeof(xlen) == 32 <->
  0b1 @ 0b0110 @ 0b01 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, MHACC_H1) if sizeof(xlen) == 32 <->
  0b1 @ 0b0111 @ 0b01 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, MHACCSU) if sizeof(xlen) == 32 <->
  0b1 @ 0b1001 @ 0b01 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, MULQ) if sizeof(xlen) == 32 <->
  0b1 @ 0b1010 @ 0b01 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMULH_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b0000 @ 0b01 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMHACC_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b0001 @ 0b01 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMULHU_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b0010 @ 0b01 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMHACCU_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b0011 @ 0b01 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMULH_W_HE) if sizeof(xlen) == 64 <->
  0b1 @ 0b0100 @ 0b01 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMHACC_W_HE) if sizeof(xlen) == 64 <->
  0b1 @ 0b0101 @ 0b01 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMULH_W_HO) if sizeof(xlen) == 64 <->
  0b1 @ 0b0110 @ 0b01 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMHACC_W_HO) if sizeof(xlen) == 64 <->
  0b1 @ 0b0111 @ 0b01 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMULHSU_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b1000 @ 0b01 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMHACCSU_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b1001 @ 0b01 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMULQ_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b1010 @ 0b01 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, MQACC_W00) if sizeof(xlen) == 64 <->
  0b1 @ 0b1101 @ 0b01 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, MQACC_W11) if sizeof(xlen) == 64 <->
  0b1 @ 0b1111 @ 0b01 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, MULHR) if sizeof(xlen) == 32 <->
  0b1 @ 0b0000 @ 0b11 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, MHRACC) if sizeof(xlen) == 32 <->
  0b1 @ 0b0001 @ 0b11 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, MULHRU) if sizeof(xlen) == 32 <->
  0b1 @ 0b0010 @ 0b11 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, MHRACCU) if sizeof(xlen) == 32 <->
  0b1 @ 0b0011 @ 0b11 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, MULHSU_H0) if sizeof(xlen) == 32 <->
  0b1 @ 0b0100 @ 0b11 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, MHACCSU_H0) if sizeof(xlen) == 32 <->
  0b1 @ 0b0101 @ 0b11 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, MULHSU_H1) if sizeof(xlen) == 32 <->
  0b1 @ 0b0110 @ 0b11 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, MHACCSU_H1) if sizeof(xlen) == 32 <->
  0b1 @ 0b0111 @ 0b11 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, MULHRSU) if sizeof(xlen) == 32 <->
  0b1 @ 0b1000 @ 0b11 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, MHRACCSU) if sizeof(xlen) == 32 <->
  0b1 @ 0b1001 @ 0b11 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, MULQR) if sizeof(xlen) == 32 <->
  0b1 @ 0b1010 @ 0b11 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMULHR_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b0000 @ 0b11 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMHRACC_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b0001 @ 0b11 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMULHRU_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b0010 @ 0b11 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMHRACCU_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b0011 @ 0b11 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMULHSU_W_HE) if sizeof(xlen) == 64 <->
  0b1 @ 0b0100 @ 0b11 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMHACCSU_W_HE) if sizeof(xlen) == 64 <->
  0b1 @ 0b0101 @ 0b11 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMULHSU_W_HO) if sizeof(xlen) == 64 <->
  0b1 @ 0b0110 @ 0b11 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMHACCSU_W_HO) if sizeof(xlen) == 64 <->
  0b1 @ 0b0111 @ 0b11 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMULHRSU_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b1000 @ 0b11 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMHRACCSU_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b1001 @ 0b11 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, PMULQR_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b1010 @ 0b11 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, MQRACC_W00) if sizeof(xlen) == 64 <->
  0b1 @ 0b1101 @ 0b11 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_MUL(rs1, rs2, rd, MQRACC_W11) if sizeof(xlen) == 64 <->
  0b1 @ 0b1111 @ 0b11 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0111011 if sizeof(xlen) == 64

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
    PMULHSU_H => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        let rs1_halfword = rs1_val[(i+15)..i];
        let rs2_halfword = rs2_val[(i+15)..i];
        result[(i+15)..i] = mulhsu(rs1_halfword, rs2_halfword);
      }
    },
    PMHACCSU_H => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        let rs1_halfword = rs1_val[(i+15)..i];
        let rs2_halfword = rs2_val[(i+15)..i];
        let rd_halfword = rd_val[(i+15)..i];
        result[(i+15)..i] = rd_halfword + mulhsu(rs1_halfword, rs2_halfword);
      }
    },
    PMULQ_H => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        let rs1_halfword = rs1_val[(i+15)..i];
        let rs2_halfword = rs2_val[(i+15)..i];
        result[(i+15)..i] = mulq(rs1_halfword, rs2_halfword)[15..0];
      }
    },
    MQACC_H00 => {
      let rs1_halfword = rs1_val[15..0];
      let rs2_halfword = rs2_val[15..0];
      result = rd_val + EXTS(mulq(rs1_halfword, rs2_halfword));
    },
    MQACC_H11 => {
      let rs1_halfword = rs1_val[31..16];
      let rs2_halfword = rs2_val[31..16];
      result = rd_val + EXTS(mulq(rs1_halfword, rs2_halfword));
    },
    PMQACC_W_HEE => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        let rs1_halfword = rs1_val[(i+15)..i];
        let rs2_halfword = rs2_val[(i+15)..i];
        let rd_word = rd_val[(i+31)..i];
        result[(i+31)..i] = rd_word + mulq(rs1_halfword, rs2_halfword);
      }
    },
    PMQACC_W_HOO => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        let rs1_halfword = rs1_val[(i+31)..(i+16)];
        let rs2_halfword = rs2_val[(i+31)..(i+16)];
        let rd_word = rd_val[(i+31)..i];
        result[(i+31)..i] = rd_word + mulq(rs1_halfword, rs2_halfword);
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
        result[(i+15)..i] = rd_halfword + mulhsu(rs1_halfword, rs2_halfword);
      }
    },
    PMULHSU_H_BO => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        let rs1_halfword = rs1_val[(i+15)..i];
        let rs2_halfword = EXTZ(16, rs2_val[(i+15)..(i+8)]);
        result[(i+15)..i] = mulhsu(rs1_halfword, rs2_halfword);
      }
    },
    PMHACCSU_H_BO => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        let rs1_halfword = rs1_val[(i+15)..i];
        let rs2_halfword = EXTZ(16, rs2_val[(i+15)..(i+8)]);
        let rd_halfword = rd_val[(i+15)..i];
        result[(i+15)..i] = rd_halfword + mulhsu(rs1_halfword, rs2_halfword);
      }
    },
    PMULHRSU_H => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        let rs1_halfword = rs1_val[(i+15)..i];
        let rs2_halfword = rs2_val[(i+15)..i];
        result[(i+15)..i] = mulhrsu(rs1_halfword, rs2_halfword);
      }
    },
    PMHRACCSU_H => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        let rs1_halfword = rs1_val[(i+15)..i];
        let rs2_halfword = rs2_val[(i+15)..i];
        let rd_halfword = rd_val[(i+15)..i];
        result[(i+15)..i] = rd_halfword + mulhrsu(rs1_halfword, rs2_halfword);
      }
    },
    PMULQR_H => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        let rs1_halfword = rs1_val[(i+15)..i];
        let rs2_halfword = rs2_val[(i+15)..i];
        result[(i+15)..i] = mulqr(rs1_halfword, rs2_halfword)[15..0];
      }
    },
    MQRACC_H00 => {
      let rs1_halfword = rs1_val[15..0];
      let rs2_halfword = rs2_val[15..0];
      result = rd_val + EXTS(mulqr(rs1_halfword, rs2_halfword));
    },
    MQRACC_H11 => {
      let rs1_halfword = rs1_val[31..16];
      let rs2_halfword = rs2_val[31..16];
      result = rd_val + EXTS(mulqr(rs1_halfword, rs2_halfword));
    },
    PMQRACC_W_HEE => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        let rs1_halfword = rs1_val[(i+15)..i];
        let rs2_halfword = rs2_val[(i+15)..i];
        result[(i+31)..i] = mulqr(rs1_halfword, rs2_halfword);
      }
    },
    PMQRACC_W_HOO => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        let rs1_halfword = rs1_val[(i+31)..(i+16)];
        let rs2_halfword = rs2_val[(i+31)..(i+16)];
        result[(i+31)..i] = mulqr(rs1_halfword, rs2_halfword);
      }
    },
    MHACC => {
      result = rd_val + mulh(rs1_val, rs2_val);
    },
    MHACCU => {
      result = rd_val + mulhu(rs1_val, rs2_val);
    },
    MULH_H0 => {
      result = mulh(rs1_val, EXTS(sizeof(xlen), rs2_val[15..0]));
    },
    MHACC_H0 => {
      result = rd_val + mulh(rs1_val, EXTS(sizeof(xlen), rs2_val[15..0]));
    },
    MULH_H1 => {
      result = mulh(rs1_val, EXTS(sizeof(xlen), rs2_val[31..16]));
    },
    MHACC_H1 => {
      result = rd_val + mulh(rs1_val, EXTS(sizeof(xlen), rs2_val[31..16]));
    },
    MHACCSU => {
      result = rd_val + mulhsu(rs1_val, rs2_val);
    },
    MULQ => {
      result = if (sizeof(xlen) == 32) then mulq(rs1_val, rs2_val)[31..0] else zeros(64);
    },
    PMULH_W => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        let rs1_word = rs1_val[(i+31)..i];
        let rs2_word = rs2_val[(i+31)..i];
        result[(i+31)..i] = mulh(rs1_word, rs2_word);
      }
    },
    PMHACC_W => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        let rs1_word = rs1_val[(i+31)..i];
        let rs2_word = rs2_val[(i+31)..i];
        let rd_word = rd_val[(i+31)..i];
        result[(i+31)..i] = rd_word + mulh(rs1_word, rs2_word);
      }
    },
    PMULHU_W => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        let rs1_word = rs1_val[(i+31)..i];
        let rs2_word = rs2_val[(i+31)..i];
        result[(i+31)..i] = mulhu(rs1_word, rs2_word);
      }
    },
    PMHACCU_W => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        let rs1_word = rs1_val[(i+31)..i];
        let rs2_word = rs2_val[(i+31)..i];
        let rd_word = rd_val[(i+31)..i];
        result[(i+31)..i] = rd_word + mulhu(rs1_word, rs2_word);
      }
    },
    PMULH_W_HE => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        let rs1_word = rs1_val[(i+31)..i];
        let rs2_word = EXTS(32, rs2_val[(i+15)..i]);
        result[(i+31)..i] = mulh(rs1_word, rs2_word);
      }
    },
    PMHACC_W_HE => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        let rs1_word = rs1_val[(i+31)..i];
        let rs2_word = EXTS(32, rs2_val[(i+15)..i]);
        let rd_word = rd_val[(i+31)..i];
        result[(i+31)..i] = rd_word + mulh(rs1_word, rs2_word);
      }
    },
    PMULH_W_HO => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        let rs1_word = rs1_val[(i+31)..i];
        let rs2_word = EXTS(32, rs2_val[(i+31)..(i+16)]);
        result[(i+31)..i] = mulh(rs1_word, rs2_word);
      }
    },
    PMHACC_W_HO => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        let rs1_word = rs1_val[(i+31)..i];
        let rs2_word = EXTS(32, rs2_val[(i+31)..(i+16)]);
        let rd_word = rd_val[(i+31)..i];
        result[(i+31)..i] = rd_word + mulh(rs1_word, rs2_word);
      }
    },
    PMULHSU_W => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        let rs1_word = rs1_val[(i+31)..i];
        let rs2_word = rs2_val[(i+31)..i];
        result[(i+31)..i] = mulhsu(rs1_word, rs2_word);
      }
    },
    PMHACCSU_W => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        let rs1_word = rs1_val[(i+31)..i];
        let rs2_word = rs2_val[(i+31)..i];
        let rd_word = rd_val[(i+31)..i];
        result[(i+31)..i] = rd_word + mulhsu(rs1_word, rs2_word);
      }
    },
    PMULQ_W => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        let rs1_word = rs1_val[(i+31)..i];
        let rs2_word = rs2_val[(i+31)..i];
        result[(i+31)..i] = mulq(rs1_word, rs2_word)[31..0];
      }
    },
    MQACC_W00 if sizeof(xlen) == 64 => {
      let rs1_word = rs1_val[31..0];
      let rs2_word = rs2_val[31..0];
      result = rd_val + mulq(rs1_word, rs2_word);
    },
    MQACC_W11 if sizeof(xlen) == 64 => {
      let rs1_word = rs1_val[63..32];
      let rs2_word = rs2_val[63..32];
      result = rd_val + mulq(rs1_word, rs2_word);
    },
    MQACC_W00 => {
      result = result; // TODO: In order to please the coverage checker.
    },
    MQACC_W11 => {
      result = result; // TODO: In order to please the coverage checker.
    },
    MULHR => {
      result = mulhr(rs1_val, rs2_val);
    },
    MHRACC => {
      result = rd_val + mulhr(rs1_val, rs2_val);
    },
    MULHRU => {
      result = mulhru(rs1_val, rs2_val);
    },
    MHRACCU => {
      result = rd_val + mulhru(rs1_val, rs2_val);
    },
    MULHSU_H0 => {
      result = mulhsu(rs1_val, EXTS(sizeof(xlen), rs2_val[15..0]));
    },
    MHACCSU_H0 => {
      result = rd_val + mulhsu(rs1_val, EXTS(sizeof(xlen), rs2_val[15..0]));
    },
    MULHSU_H1 => {
      result = mulhsu(rs1_val, EXTS(sizeof(xlen), rs2_val[31..16]));
    },
    MHACCSU_H1 => {
      result = rd_val + mulhsu(rs1_val, EXTS(sizeof(xlen), rs2_val[31..16]));
    },
    MULHRSU => {
      result = mulhrsu(rs1_val, rs2_val);
    },
    MHRACCSU => {
      result = rd_val + mulhrsu(rs1_val, rs2_val);
    },
    MULQR => {
      result = if (sizeof(xlen) == 32) then mulqr(rs1_val, rs2_val)[31..0] else zeros(64);
    },
    PMULHR_W => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        let rs1_word = rs1_val[(i+31)..i];
        let rs2_word = rs2_val[(i+31)..i];
        result[(i+31)..i] = mulhr(rs1_word, rs2_word);
      }
    },
    PMHRACC_W => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        let rs1_word = rs1_val[(i+31)..i];
        let rs2_word = rs2_val[(i+31)..i];
        let rd_word = rd_val[(i+31)..i];
        result[(i+31)..i] = rd_word + mulhr(rs1_word, rs2_word);
      }
    },
    PMULHRU_W => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        let rs1_word = rs1_val[(i+31)..i];
        let rs2_word = rs2_val[(i+31)..i];
        result[(i+31)..i] = mulhru(rs1_word, rs2_word);
      }
    },
    PMHRACCU_W => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        let rs1_word = rs1_val[(i+31)..i];
        let rs2_word = rs2_val[(i+31)..i];
        let rd_word = rd_val[(i+31)..i];
        result[(i+31)..i] = rd_word + mulhru(rs1_word, rs2_word);
      }
    },
    PMULHSU_W_HE => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        let rs1_word = rs1_val[(i+31)..i];
        let rs2_word = EXTS(32, rs2_val[(i+15)..i]);
        result[(i+31)..i] = mulhsu(rs1_word, rs2_word);
      }
    },
    PMHACCSU_W_HE => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        let rs1_word = rs1_val[(i+31)..i];
        let rs2_word = EXTS(32, rs2_val[(i+15)..i]);
        let rd_word = rd_val[(i+31)..i];
        result[(i+31)..i] = rd_word + mulhsu(rs1_word, rs2_word);
      }
    },
    PMULHSU_W_HO => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        let rs1_word = rs1_val[(i+31)..i];
        let rs2_word = EXTS(32, rs2_val[(i+31)..(i+16)]);
        result[(i+31)..i] = mulhsu(rs1_word, rs2_word);
      }
    },
    PMHACCSU_W_HO => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        let rs1_word = rs1_val[(i+31)..i];
        let rs2_word = EXTS(32, rs2_val[(i+31)..(i+16)]);
        let rd_word = rd_val[(i+31)..i];
        result[(i+31)..i] = rd_word + mulhsu(rs1_word, rs2_word);
      }
    },
    PMULHRSU_W => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        let rs1_word = rs1_val[(i+31)..i];
        let rs2_word = rs2_val[(i+31)..i];
        result[(i+31)..i] = mulhrsu(rs1_word, rs2_word);
      }
    },
    PMHRACCSU_W => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        let rs1_word = rs1_val[(i+31)..i];
        let rs2_word = rs2_val[(i+31)..i];
        let rd_word = rd_val[(i+31)..i];
        result[(i+31)..i] = rd_word + mulhrsu(rs1_word, rs2_word);
      }
    },
    PMULQR_W => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        let rs1_word = rs1_val[(i+31)..i];
        let rs2_word = rs2_val[(i+31)..i];
        result[(i+31)..i] = mulqr(rs1_word, rs2_word)[31..0];
      }
    },
    MQRACC_W00 if sizeof(xlen) == 64 => {
      let rs1_word = rs1_val[31..0];
      let rs2_word = rs2_val[31..0];
      result = rd_val + mulqr(rs1_word, rs2_word);
    },
    MQRACC_W11 if sizeof(xlen) == 64 => {
      let rs1_word = rs1_val[63..32];
      let rs2_word = rs2_val[63..32];
      result = rd_val + mulqr(rs1_word, rs2_word);
    },
    MQRACC_W00 => {
      result = result; // TODO: In order to please the coverage checker.
    },
    MQRACC_W11 => {
      result = result; // TODO: In order to please the coverage checker.
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
  PMULHSU_H <-> "pmulhsu.h",
  PMHACCSU_H <-> "pmhaccsu.h",
  PMULQ_H <-> "pmulq.h",
  MQACC_H00 <-> "mqacc.h00",
  MQACC_H11 <-> "mqacc.h11",
  PMQACC_W_HEE <-> "pmqacc.w.hee",
  PMQACC_W_HOO <-> "pmqacc.w.hoo",
  PMULHR_H <-> "pmulhr.h",
  PMHRACC_H <-> "pmhracc.h",
  PMULHRU_H <-> "pmulhru.h",
  PMHRACCU_H <-> "pmhraccu.h",
  PMULHSU_H_BE <-> "pmulhsu.h.be",
  PMHACCSU_H_BE <-> "pmhaccsu.h.be",
  PMULHSU_H_BO <-> "pmulhsu.h.bo",
  PMHACCSU_H_BO <-> "pmhaccsu.h.bo",
  PMULHRSU_H <-> "pmulhrsu.h",
  PMHRACCSU_H <-> "pmhraccsu.h",
  PMULQR_H <-> "pmulqr.h",
  MQRACC_H00 <-> "mqracc.h00",
  MQRACC_H11 <-> "mqracc.h11",
  PMQRACC_W_HEE <-> "pmqracc.w.hee",
  PMQRACC_W_HOO <-> "pmqracc.w.hoo",
  MHACC <-> "mhacc",
  MHACCU <-> "mhaccu",
  MULH_H0 <-> "mulh.h0",
  MHACC_H0 <-> "mhacc.h0",
  MULH_H1 <-> "mulh.h1",
  MHACC_H1 <-> "mhacc.h1",
  MHACCSU <-> "mhaccsu",
  MULQ <-> "mulq",
  PMULH_W <-> "pmulh.w",
  PMHACC_W <-> "pmhacc.w",
  PMULHU_W <-> "pmulhu.w",
  PMHACCU_W <-> "pmhaccu.w",
  PMULH_W_HE <-> "pmulh.w.he",
  PMHACC_W_HE <-> "pmhacc.w.he",
  PMULH_W_HO <-> "pmulh.w.ho",
  PMHACC_W_HO <-> "pmhacc.w.ho",
  PMULHSU_W <-> "pmulhsu.w",
  PMHACCSU_W <-> "pmhaccsu.w",
  PMULQ_W <-> "pmulq.w",
  MQACC_W00 <-> "mqacc.w00",
  MQACC_W11 <-> "mqacc.w11",
  MULHR <-> "mulhr",
  MHRACC <-> "mhracc",
  MULHRU <-> "mulhru",
  MHRACCU <-> "mhraccu",
  MULHSU_H0 <-> "mulhsu.h0",
  MHACCSU_H0 <-> "mhaccsu.h0",
  MULHSU_H1 <-> "mulhsu.h1",
  MHACCSU_H1 <-> "mhaccsu.h1",
  MULHRSU <-> "mulhrsu",
  MHRACCSU <-> "mhraccsu",
  MULQR <-> "mulqr",
  PMULHR_W <-> "pmulhr.w",
  PMHRACC_W <-> "pmhracc.w",
  PMULHRU_W <-> "pmulhru.w",
  PMHRACCU_W <-> "pmhraccu.w",
  PMULHSU_W_HE <-> "pmulhsu.w.he",
  PMHACCSU_W_HE <-> "pmhaccsu.w.he",
  PMULHSU_W_HO <-> "pmulhsu.w.ho",
  PMHACCSU_W_HO <-> "pmhaccsu.w.ho",
  PMULHRSU_W <-> "pmulhrsu.w",
  PMHRACCSU_W <-> "pmhraccsu.w",
  PMULQR_W <-> "pmulqr.w",
  MQRACC_W00 <-> "mqracc.w00",
  MQRACC_W11 <-> "mqracc.w11"
}

mapping clause assembly = PEXT_MUL(rs1, rs2, rd, p_inst)
  <-> p_mul_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)