chapter \<open>Generated by Lem from \<open>handwritten_support/riscv_extras.lem\<close>.\<close>

theory "Riscv_extras" 

imports
  Main
  "LEM.Lem_pervasives"
  "LEM.Lem_pervasives_extra"
  "Sail.Sail2_instr_kinds"
  "Sail.Sail2_values"
  "Sail.Sail2_operators_mwords"
  "Sail.Sail2_prompt_monad"
  "Sail.Sail2_prompt"

begin 

\<comment> \<open>\<open>open import Pervasives\<close>\<close>
\<comment> \<open>\<open>open import Pervasives_extra\<close>\<close>
\<comment> \<open>\<open>open import Sail2_instr_kinds\<close>\<close>
\<comment> \<open>\<open>open import Sail2_values\<close>\<close>
\<comment> \<open>\<open>open import Sail2_operators_mwords\<close>\<close>
\<comment> \<open>\<open>open import Sail2_prompt_monad\<close>\<close>
\<comment> \<open>\<open>open import Sail2_prompt\<close>\<close>

type_synonym 'a bitvector =" ( 'a::len)Word.word "

definition MEM_fence_rw_rw  :: " unit \<Rightarrow>('b,(unit),'a)monad "  where 
     " MEM_fence_rw_rw _ = ( barrier Barrier_RISCV_rw_rw )"

definition MEM_fence_r_rw  :: " unit \<Rightarrow>('b,(unit),'a)monad "  where 
     " MEM_fence_r_rw  _ = ( barrier Barrier_RISCV_r_rw )"

definition MEM_fence_r_r  :: " unit \<Rightarrow>('b,(unit),'a)monad "  where 
     " MEM_fence_r_r   _ = ( barrier Barrier_RISCV_r_r )"

definition MEM_fence_rw_w  :: " unit \<Rightarrow>('b,(unit),'a)monad "  where 
     " MEM_fence_rw_w  _ = ( barrier Barrier_RISCV_rw_w )"

definition MEM_fence_w_w  :: " unit \<Rightarrow>('b,(unit),'a)monad "  where 
     " MEM_fence_w_w   _ = ( barrier Barrier_RISCV_w_w )"

definition MEM_fence_w_rw  :: " unit \<Rightarrow>('b,(unit),'a)monad "  where 
     " MEM_fence_w_rw  _ = ( barrier Barrier_RISCV_w_rw )"

definition MEM_fence_rw_r  :: " unit \<Rightarrow>('b,(unit),'a)monad "  where 
     " MEM_fence_rw_r  _ = ( barrier Barrier_RISCV_rw_r )"

definition MEM_fence_r_w  :: " unit \<Rightarrow>('b,(unit),'a)monad "  where 
     " MEM_fence_r_w   _ = ( barrier Barrier_RISCV_r_w )"

definition MEM_fence_w_r  :: " unit \<Rightarrow>('b,(unit),'a)monad "  where 
     " MEM_fence_w_r   _ = ( barrier Barrier_RISCV_w_r )"

definition MEM_fence_tso  :: " unit \<Rightarrow>('b,(unit),'a)monad "  where 
     " MEM_fence_tso   _ = ( barrier Barrier_RISCV_tso )"

definition MEM_fence_i  :: " unit \<Rightarrow>('b,(unit),'a)monad "  where 
     " MEM_fence_i     _ = ( barrier Barrier_RISCV_i )"


\<comment> \<open>\<open>val MEMea                            : forall 'rv 'a 'e. Size 'a => bitvector 'a -> integer -> monad 'rv unit 'e\<close>\<close>
\<comment> \<open>\<open>val MEMea_release                    : forall 'rv 'a 'e. Size 'a => bitvector 'a -> integer -> monad 'rv unit 'e\<close>\<close>
\<comment> \<open>\<open>val MEMea_strong_release             : forall 'rv 'a 'e. Size 'a => bitvector 'a -> integer -> monad 'rv unit 'e\<close>\<close>
\<comment> \<open>\<open>val MEMea_conditional                : forall 'rv 'a 'e. Size 'a => bitvector 'a -> integer -> monad 'rv unit 'e\<close>\<close>
\<comment> \<open>\<open>val MEMea_conditional_release        : forall 'rv 'a 'e. Size 'a => bitvector 'a -> integer -> monad 'rv unit 'e\<close>\<close>
\<comment> \<open>\<open>val MEMea_conditional_strong_release : forall 'rv 'a 'e. Size 'a => bitvector 'a -> integer -> monad 'rv unit 'e\<close>\<close>

definition MEMea  :: "('a::len)Word.word \<Rightarrow> int \<Rightarrow>('rv,(unit),'e)monad "                       where 
     " MEMea addr size1                      = ( write_mem_ea 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict Write_plain ()  addr size1 )" 
  for  addr  :: "('a::len)Word.word " 
  and  size1  :: " int "

definition MEMea_release  :: "('a::len)Word.word \<Rightarrow> int \<Rightarrow>('rv,(unit),'e)monad "               where 
     " MEMea_release addr size1              = ( write_mem_ea 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict Write_RISCV_release ()  addr size1 )" 
  for  addr  :: "('a::len)Word.word " 
  and  size1  :: " int "

definition MEMea_strong_release  :: "('a::len)Word.word \<Rightarrow> int \<Rightarrow>('rv,(unit),'e)monad "        where 
     " MEMea_strong_release addr size1       = ( write_mem_ea 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict Write_RISCV_strong_release ()  addr size1 )" 
  for  addr  :: "('a::len)Word.word " 
  and  size1  :: " int "

definition MEMea_conditional  :: "('a::len)Word.word \<Rightarrow> int \<Rightarrow>('rv,(unit),'e)monad "           where 
     " MEMea_conditional addr size1          = ( write_mem_ea 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict Write_RISCV_conditional ()  addr size1 )" 
  for  addr  :: "('a::len)Word.word " 
  and  size1  :: " int "

definition MEMea_conditional_release  :: "('a::len)Word.word \<Rightarrow> int \<Rightarrow>('rv,(unit),'e)monad "   where 
     " MEMea_conditional_release addr size1  = ( write_mem_ea 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict Write_RISCV_conditional_release ()  addr size1 )" 
  for  addr  :: "('a::len)Word.word " 
  and  size1  :: " int "

definition MEMea_conditional_strong_release  :: "('a::len)Word.word \<Rightarrow> int \<Rightarrow>('rv,(unit),'e)monad " 
                                          where 
     " MEMea_conditional_strong_release addr size1
                                          = ( write_mem_ea 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict Write_RISCV_conditional_strong_release ()  addr size1 )" 
  for  addr  :: "('a::len)Word.word " 
  and  size1  :: " int "


\<comment> \<open>\<open>val MEMr                         : forall 'rv 'a 'b 'e. Size 'a, Size 'b => integer -> integer -> bitvector 'a -> bitvector 'a -> monad 'rv (bitvector 'b) 'e\<close>\<close>
\<comment> \<open>\<open>val MEMr_acquire                 : forall 'rv 'a 'b 'e. Size 'a, Size 'b => integer -> integer -> bitvector 'a -> bitvector 'a -> monad 'rv (bitvector 'b) 'e\<close>\<close>
\<comment> \<open>\<open>val MEMr_strong_acquire          : forall 'rv 'a 'b 'e. Size 'a, Size 'b => integer -> integer -> bitvector 'a -> bitvector 'a -> monad 'rv (bitvector 'b) 'e\<close>\<close>
\<comment> \<open>\<open>val MEMr_reserved                : forall 'rv 'a 'b 'e. Size 'a, Size 'b => integer -> integer -> bitvector 'a -> bitvector 'a -> monad 'rv (bitvector 'b) 'e\<close>\<close>
\<comment> \<open>\<open>val MEMr_reserved_acquire        : forall 'rv 'a 'b 'e. Size 'a, Size 'b => integer -> integer -> bitvector 'a -> bitvector 'a -> monad 'rv (bitvector 'b) 'e\<close>\<close>
\<comment> \<open>\<open>val MEMr_reserved_strong_acquire : forall 'rv 'a 'b 'e. Size 'a, Size 'b => integer -> integer -> bitvector 'a -> bitvector 'a -> monad 'rv (bitvector 'b) 'e\<close>\<close>

definition MEMr  :: " int \<Rightarrow> int \<Rightarrow>('a::len)Word.word \<Rightarrow>('a::len)Word.word \<Rightarrow>('rv,(('b::len)Word.word),'e)monad "                          where 
     " MEMr addrsize size1 hexRAM addr                         = ( read_mem 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Bitvector_Machine_word_mword_dict Read_plain addrsize addr size1 )" 
  for  addrsize  :: " int " 
  and  size1  :: " int " 
  and  hexRAM  :: "('a::len)Word.word " 
  and  addr  :: "('a::len)Word.word "

definition MEMr_acquire  :: " int \<Rightarrow> int \<Rightarrow>('a::len)Word.word \<Rightarrow>('a::len)Word.word \<Rightarrow>('rv,(('b::len)Word.word),'e)monad "                  where 
     " MEMr_acquire addrsize size1 hexRAM addr                 = ( read_mem 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Bitvector_Machine_word_mword_dict Read_RISCV_acquire addrsize addr size1 )" 
  for  addrsize  :: " int " 
  and  size1  :: " int " 
  and  hexRAM  :: "('a::len)Word.word " 
  and  addr  :: "('a::len)Word.word "

definition MEMr_strong_acquire  :: " int \<Rightarrow> int \<Rightarrow>('a::len)Word.word \<Rightarrow>('a::len)Word.word \<Rightarrow>('rv,(('b::len)Word.word),'e)monad "           where 
     " MEMr_strong_acquire addrsize size1 hexRAM addr          = ( read_mem 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Bitvector_Machine_word_mword_dict Read_RISCV_strong_acquire addrsize addr size1 )" 
  for  addrsize  :: " int " 
  and  size1  :: " int " 
  and  hexRAM  :: "('a::len)Word.word " 
  and  addr  :: "('a::len)Word.word "

definition MEMr_reserved  :: " int \<Rightarrow> int \<Rightarrow>('a::len)Word.word \<Rightarrow>('a::len)Word.word \<Rightarrow>('rv,(('b::len)Word.word),'e)monad "                 where 
     " MEMr_reserved addrsize size1 hexRAM addr                = ( read_mem 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Bitvector_Machine_word_mword_dict Read_RISCV_reserved addrsize addr size1 )" 
  for  addrsize  :: " int " 
  and  size1  :: " int " 
  and  hexRAM  :: "('a::len)Word.word " 
  and  addr  :: "('a::len)Word.word "

definition MEMr_reserved_acquire  :: " int \<Rightarrow> int \<Rightarrow>('a::len)Word.word \<Rightarrow>('a::len)Word.word \<Rightarrow>('rv,(('b::len)Word.word),'e)monad "         where 
     " MEMr_reserved_acquire addrsize size1 hexRAM addr        = ( read_mem 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Bitvector_Machine_word_mword_dict Read_RISCV_reserved_acquire addrsize addr size1 )" 
  for  addrsize  :: " int " 
  and  size1  :: " int " 
  and  hexRAM  :: "('a::len)Word.word " 
  and  addr  :: "('a::len)Word.word "

definition MEMr_reserved_strong_acquire  :: " int \<Rightarrow> int \<Rightarrow>('a::len)Word.word \<Rightarrow>('a::len)Word.word \<Rightarrow>('rv,(('b::len)Word.word),'e)monad "  where 
     " MEMr_reserved_strong_acquire addrsize size1 hexRAM addr = ( read_mem 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Bitvector_Machine_word_mword_dict Read_RISCV_reserved_strong_acquire addrsize addr size1 )" 
  for  addrsize  :: " int " 
  and  size1  :: " int " 
  and  hexRAM  :: "('a::len)Word.word " 
  and  addr  :: "('a::len)Word.word "


\<comment> \<open>\<open>val MEMw                            : forall 'rv 'a 'b 'e. Size 'a, Size 'b => integer -> integer -> bitvector 'a -> bitvector 'a -> bitvector 'b -> monad 'rv bool 'e\<close>\<close>
\<comment> \<open>\<open>val MEMw_release                    : forall 'rv 'a 'b 'e. Size 'a, Size 'b => integer -> integer -> bitvector 'a -> bitvector 'a -> bitvector 'b -> monad 'rv bool 'e\<close>\<close>
\<comment> \<open>\<open>val MEMw_strong_release             : forall 'rv 'a 'b 'e. Size 'a, Size 'b => integer -> integer -> bitvector 'a -> bitvector 'a -> bitvector 'b -> monad 'rv bool 'e\<close>\<close>
\<comment> \<open>\<open>val MEMw_conditional                : forall 'rv 'a 'b 'e. Size 'a, Size 'b => integer -> integer -> bitvector 'a -> bitvector 'a -> bitvector 'b -> monad 'rv bool 'e\<close>\<close>
\<comment> \<open>\<open>val MEMw_conditional_release        : forall 'rv 'a 'b 'e. Size 'a, Size 'b => integer -> integer -> bitvector 'a -> bitvector 'a -> bitvector 'b -> monad 'rv bool 'e\<close>\<close>
\<comment> \<open>\<open>val MEMw_conditional_strong_release : forall 'rv 'a 'b 'e. Size 'a, Size 'b => integer -> integer -> bitvector 'a -> bitvector 'a -> bitvector 'b -> monad 'rv bool 'e\<close>\<close>

definition MEMw  :: " int \<Rightarrow> int \<Rightarrow>('a::len)Word.word \<Rightarrow>('a::len)Word.word \<Rightarrow>('b::len)Word.word \<Rightarrow>('rv,(bool),'e)monad "                             where 
     " MEMw addrsize size1 hexRAM addr                            = ( write_mem 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Bitvector_Machine_word_mword_dict Write_plain addrsize addr size1 )" 
  for  addrsize  :: " int " 
  and  size1  :: " int " 
  and  hexRAM  :: "('a::len)Word.word " 
  and  addr  :: "('a::len)Word.word "

definition MEMw_release  :: " int \<Rightarrow> int \<Rightarrow>('a::len)Word.word \<Rightarrow>('a::len)Word.word \<Rightarrow>('b::len)Word.word \<Rightarrow>('rv,(bool),'e)monad "                     where 
     " MEMw_release addrsize size1 hexRAM addr                    = ( write_mem 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Bitvector_Machine_word_mword_dict Write_RISCV_release addrsize addr size1 )" 
  for  addrsize  :: " int " 
  and  size1  :: " int " 
  and  hexRAM  :: "('a::len)Word.word " 
  and  addr  :: "('a::len)Word.word "

definition MEMw_strong_release  :: " int \<Rightarrow> int \<Rightarrow>('a::len)Word.word \<Rightarrow>('a::len)Word.word \<Rightarrow>('b::len)Word.word \<Rightarrow>('rv,(bool),'e)monad "              where 
     " MEMw_strong_release addrsize size1 hexRAM addr             = ( write_mem 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Bitvector_Machine_word_mword_dict Write_RISCV_strong_release addrsize addr size1 )" 
  for  addrsize  :: " int " 
  and  size1  :: " int " 
  and  hexRAM  :: "('a::len)Word.word " 
  and  addr  :: "('a::len)Word.word "

definition MEMw_conditional  :: " int \<Rightarrow> int \<Rightarrow>('a::len)Word.word \<Rightarrow>('a::len)Word.word \<Rightarrow>('b::len)Word.word \<Rightarrow>('rv,(bool),'e)monad "                 where 
     " MEMw_conditional addrsize size1 hexRAM addr                = ( write_mem 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Bitvector_Machine_word_mword_dict Write_RISCV_conditional addrsize addr size1 )" 
  for  addrsize  :: " int " 
  and  size1  :: " int " 
  and  hexRAM  :: "('a::len)Word.word " 
  and  addr  :: "('a::len)Word.word "

definition MEMw_conditional_release  :: " int \<Rightarrow> int \<Rightarrow>('a::len)Word.word \<Rightarrow>('a::len)Word.word \<Rightarrow>('b::len)Word.word \<Rightarrow>('rv,(bool),'e)monad "         where 
     " MEMw_conditional_release addrsize size1 hexRAM addr        = ( write_mem 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Bitvector_Machine_word_mword_dict Write_RISCV_conditional_release addrsize addr size1 )" 
  for  addrsize  :: " int " 
  and  size1  :: " int " 
  and  hexRAM  :: "('a::len)Word.word " 
  and  addr  :: "('a::len)Word.word "

definition MEMw_conditional_strong_release  :: " int \<Rightarrow> int \<Rightarrow>('a::len)Word.word \<Rightarrow>('a::len)Word.word \<Rightarrow>('b::len)Word.word \<Rightarrow>('rv,(bool),'e)monad "  where 
     " MEMw_conditional_strong_release addrsize size1 hexRAM addr = ( write_mem 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Bitvector_Machine_word_mword_dict Write_RISCV_conditional_strong_release addrsize addr size1 )" 
  for  addrsize  :: " int " 
  and  size1  :: " int " 
  and  hexRAM  :: "('a::len)Word.word " 
  and  addr  :: "('a::len)Word.word "


\<comment> \<open>\<open>val load_reservation : forall 'a. Size 'a => bitvector 'a -> unit\<close>\<close>
definition load_reservation  :: "('a::len)Word.word \<Rightarrow> unit "  where 
     " load_reservation addr = ( ()  )" 
  for  addr  :: "('a::len)Word.word "


definition speculate_conditional_success  :: " unit \<Rightarrow>('b,(bool),'a)monad "  where 
     " speculate_conditional_success _ = ( excl_result ()  )"


definition match_reservation  :: " 'a \<Rightarrow> bool "  where 
     " match_reservation _ = ( True )"

definition cancel_reservation  :: " unit \<Rightarrow> unit "  where 
     " cancel_reservation _ = ( ()  )"


\<comment> \<open>\<open>val sys_enable_writable_misa : unit -> bool\<close>\<close>
definition sys_enable_writable_misa  :: " unit \<Rightarrow> bool "  where 
     " sys_enable_writable_misa _ = ( True )"


\<comment> \<open>\<open>val sys_enable_rvc : unit -> bool\<close>\<close>
definition sys_enable_rvc  :: " unit \<Rightarrow> bool "  where 
     " sys_enable_rvc _ = ( True )"


\<comment> \<open>\<open>val plat_ram_base : forall 'a. Size 'a => unit -> bitvector 'a\<close>\<close>
definition plat_ram_base  :: " unit \<Rightarrow>('a::len)Word.word "  where 
     " plat_ram_base _ = ( Word.word_of_int(( 0 :: int)))"


\<comment> \<open>\<open>val plat_ram_size : forall 'a. Size 'a => unit -> bitvector 'a\<close>\<close>
definition plat_ram_size  :: " unit \<Rightarrow>('a::len)Word.word "  where 
     " plat_ram_size _ = ( Word.word_of_int(( 0 :: int)))"


\<comment> \<open>\<open>val plat_rom_base : forall 'a. Size 'a => unit -> bitvector 'a\<close>\<close>
definition plat_rom_base  :: " unit \<Rightarrow>('a::len)Word.word "  where 
     " plat_rom_base _ = ( Word.word_of_int(( 0 :: int)))"


\<comment> \<open>\<open>val plat_rom_size : forall 'a. Size 'a => unit -> bitvector 'a\<close>\<close>
definition plat_rom_size  :: " unit \<Rightarrow>('a::len)Word.word "  where 
     " plat_rom_size _ = ( Word.word_of_int(( 0 :: int)))"


\<comment> \<open>\<open>val plat_clint_base : forall 'a. Size 'a => unit -> bitvector 'a\<close>\<close>
definition plat_clint_base  :: " unit \<Rightarrow>('a::len)Word.word "  where 
     " plat_clint_base _ = ( Word.word_of_int(( 0 :: int)))"


\<comment> \<open>\<open>val plat_clint_size : forall 'a. Size 'a => unit -> bitvector 'a\<close>\<close>
definition plat_clint_size  :: " unit \<Rightarrow>('a::len)Word.word "  where 
     " plat_clint_size _ = ( Word.word_of_int(( 0 :: int)))"


\<comment> \<open>\<open>val plat_enable_dirty_update : unit -> bool\<close>\<close>
definition plat_enable_dirty_update  :: " unit \<Rightarrow> bool "  where 
     " plat_enable_dirty_update _ = ( False )"


\<comment> \<open>\<open>val plat_enable_misaligned_access : unit -> bool\<close>\<close>
definition plat_enable_misaligned_access  :: " unit \<Rightarrow> bool "  where 
     " plat_enable_misaligned_access _ = ( False )"


\<comment> \<open>\<open>val plat_enable_pmp : unit -> bool\<close>\<close>
definition plat_enable_pmp  :: " unit \<Rightarrow> bool "  where 
     " plat_enable_pmp _ = ( False )"


\<comment> \<open>\<open>val plat_mtval_has_illegal_inst_bits : unit -> bool\<close>\<close>
definition plat_mtval_has_illegal_inst_bits  :: " unit \<Rightarrow> bool "  where 
     " plat_mtval_has_illegal_inst_bits _ = ( False )"


\<comment> \<open>\<open>val plat_insns_per_tick : unit -> integer\<close>\<close>
definition plat_insns_per_tick  :: " unit \<Rightarrow> int "  where 
     " plat_insns_per_tick _ = (( 1 :: int))"


\<comment> \<open>\<open>val plat_htif_tohost : forall 'a. Size 'a => unit -> bitvector 'a\<close>\<close>
definition plat_htif_tohost  :: " unit \<Rightarrow>('a::len)Word.word "  where 
     " plat_htif_tohost _ = ( Word.word_of_int(( 0 :: int)))"


\<comment> \<open>\<open>val plat_term_write : forall 'a. Size 'a => bitvector 'a -> unit\<close>\<close>
definition plat_term_write  :: "('a::len)Word.word \<Rightarrow> unit "  where 
     " plat_term_write _ = ( ()  )"


\<comment> \<open>\<open>val plat_term_read : forall 'a. Size 'a => unit -> bitvector 'a\<close>\<close>
definition plat_term_read  :: " unit \<Rightarrow>('a::len)Word.word "  where 
     " plat_term_read _ = ( Word.word_of_int(( 0 :: int)))"


\<comment> \<open>\<open>val shift_bits_right : forall 'a 'b. Size 'a, Size 'b => bitvector 'a -> bitvector 'b -> bitvector 'a\<close>\<close>
definition shift_bits_right  :: "('a::len)Word.word \<Rightarrow>('b::len)Word.word \<Rightarrow>('a::len)Word.word "  where 
     " shift_bits_right v m = ( shiftr v (Word.uint m))" 
  for  v  :: "('a::len)Word.word " 
  and  m  :: "('b::len)Word.word "

\<comment> \<open>\<open>val shift_bits_left : forall 'a 'b. Size 'a, Size 'b => bitvector 'a -> bitvector 'b -> bitvector 'a\<close>\<close>
definition shift_bits_left  :: "('a::len)Word.word \<Rightarrow>('b::len)Word.word \<Rightarrow>('a::len)Word.word "  where 
     " shift_bits_left v m = ( shiftl v (Word.uint m))" 
  for  v  :: "('a::len)Word.word " 
  and  m  :: "('b::len)Word.word "


\<comment> \<open>\<open>val print_string : string -> string -> unit\<close>\<close>
definition print_string  :: " string \<Rightarrow> string \<Rightarrow> unit "  where 
     " print_string msg s = ( ()  )" 
  for  msg  :: " string " 
  and  s  :: " string "
 \<comment> \<open>\<open> print_endline (msg ^ s) \<close>\<close>

\<comment> \<open>\<open>val prerr_string : string -> string -> unit\<close>\<close>
definition prerr_string  :: " string \<Rightarrow> string \<Rightarrow> unit "  where 
     " prerr_string msg s = ( prerr_endline (msg @ s))" 
  for  msg  :: " string " 
  and  s  :: " string "


\<comment> \<open>\<open>val prerr_bits : forall 'a. Size 'a => string -> bitvector 'a -> unit\<close>\<close>
definition prerr_bits  :: " string \<Rightarrow>('a::len)Word.word \<Rightarrow> unit "  where 
     " prerr_bits msg bs = ( prerr_endline (msg @ (show_bitlist (List.map bitU_of_bool (Word.to_bl bs)))))" 
  for  msg  :: " string " 
  and  bs  :: "('a::len)Word.word "


\<comment> \<open>\<open>val print_bits : forall 'a. Size 'a => string -> bitvector 'a -> unit\<close>\<close>
definition print_bits0  :: " string \<Rightarrow>('a::len)Word.word \<Rightarrow> unit "  where 
     " print_bits0 msg bs = ( ()  )" 
  for  msg  :: " string " 
  and  bs  :: "('a::len)Word.word "
 \<comment> \<open>\<open> print_endline (msg ^ (show_bitlist (bits_of bs))) \<close>\<close>

\<comment> \<open>\<open>val print_dbg : string -> unit\<close>\<close>
definition print_dbg  :: " string \<Rightarrow> unit "  where 
     " print_dbg msg = ( ()  )" 
  for  msg  :: " string "

end