// TODO: I don't understand the following code so please check it.

union clause ast = PEXT_P11 : (regidx, regidx, regidx, p_p11)

mapping clause encdec = PEXT_P11(rs1, rs2, rd, MVM) <->
  0b1 @ 0b0101 @ 0b00 @ rs2 @ rs1 @ 0b001 @ rd @ 0b0111011
mapping clause encdec = PEXT_P11(rs1, rs2, rd, MVMN) <->
  0b1 @ 0b0101 @ 0b01 @ rs2 @ rs1 @ 0b001 @ rd @ 0b0111011
mapping clause encdec = PEXT_P11(rs1, rs2, rd, MERGE) <->
  0b1 @ 0b0101 @ 0b10 @ rs2 @ rs1 @ 0b001 @ rd @ 0b0111011
mapping clause encdec = PEXT_P11(rs1, rs2, rd, SRX) <->
  0b1 @ 0b0101 @ 0b11 @ rs2 @ rs1 @ 0b001 @ rd @ 0b0111011

function clause execute (PEXT_P11(rs1, rs2, rd, op)) = {
  match op {
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
    }
  };
  RETIRE_SUCCESS
}