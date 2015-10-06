theory CrashHoare
imports "Monads/NonDetMonadVCG"
begin

lemma hoare_pre_conj_const:
  "(P \<Longrightarrow> \<lbrace> Q \<rbrace> f \<lbrace> R \<rbrace>) \<Longrightarrow> \<lbrace> \<lambda>s. P \<and> Q s \<rbrace> f \<lbrace> R \<rbrace>"
  by(cases P, auto)

lemma alternativeE_valid:
  "\<lbrace> A \<rbrace> f \<lbrace> B \<rbrace>, \<lbrace> C \<rbrace> \<Longrightarrow> \<lbrace> A \<rbrace> g \<lbrace> B \<rbrace>, \<lbrace> C \<rbrace> \<Longrightarrow> \<lbrace> A \<rbrace> f OR g \<lbrace> B \<rbrace>, \<lbrace> C \<rbrace>"
  unfolding validE_def by(auto intro:alternative_valid)

section "The Crash Monad"
type_synonym ('s,'a) crash_monad = "('s, unit + 'a) nondet_monad"

text {* A process in the crash monad can terminate abruptly at any point.  We model this with
  a unit exception. *}
definition
  crash_atom :: "('s,'a) nondet_monad \<Rightarrow> ('s,'a) crash_monad"
where
  "crash_atom m = (liftE m OR throwError ())"
 
text {* The process must establish its crash invariant at the boundaries of atomic operations. *}
lemma valid_crash_atom:
  assumes valid_suc: "\<lbrace> A \<rbrace> f \<lbrace> B \<rbrace>"
      and crash:     "\<And>s. A s \<Longrightarrow> Cr () s"
  shows "\<lbrace> A \<rbrace> crash_atom f \<lbrace> B \<rbrace>, \<lbrace> Cr \<rbrace>"
  unfolding crash_atom_def
  by(wp add:alternativeE_valid valid_suc crash, auto)

section "A Crash-Safe Algorithm"

text {* We have a heap built from two-element cells.  These elements can only be updated
  one at a time, but we will insist that all indexed cells have their left and right elements
  equal. *}
record cell =
  left :: nat
  right :: nat

record heap =
  cells :: "nat \<Rightarrow> cell"
  index :: "nat \<Rightarrow> nat"
  index_length :: nat

definition
  occupied :: "heap \<Rightarrow> nat set"
where
  "occupied h = {n. \<exists>m < index_length h. index h m = n}"

text {* All cells reachable from the index. *}
definition
  lift_cells :: "heap \<Rightarrow> cell set"
where
  "lift_cells h = (\<lambda>n. cells h (index h n)) ` {n. n < index_length h}"

text {* This is the heap invariant, that must hold even on a crash. *}
definition
  valid_cells :: "cell set \<Rightarrow> bool"
where
  "valid_cells C \<longleftrightarrow> (\<forall>c\<in>C. left c = right c)"

definition
  valid_heap :: "heap \<Rightarrow> bool"
where
  "valid_heap h \<longleftrightarrow> valid_cells (lift_cells h)"

section "Crash-Atomic Updates"

text {* The elements of a cell can be updated atomically, but not whole cells.  Also, the
  index cannot be updated atomically with its length indicator. *}

definition write_left :: "nat \<Rightarrow> nat \<Rightarrow> (heap, unit) crash_monad"
where
  "write_left n l =
    crash_atom (modify (\<lambda>h. h\<lparr> cells := (cells h)(n := (cells h n)\<lparr> left := l \<rparr>) \<rparr>))"

definition write_right :: "nat \<Rightarrow> nat \<Rightarrow> (heap, unit) crash_monad"
where
  "write_right n l =
    crash_atom (modify (\<lambda>h. h\<lparr> cells := (cells h)(n := (cells h n)\<lparr> right := l \<rparr>) \<rparr>))"

definition write_index :: "nat \<Rightarrow> nat \<Rightarrow> (heap, unit) crash_monad"
where
  "write_index m n =
    crash_atom (modify (\<lambda>h. h\<lparr> index := (index h)(m := n) \<rparr>))"

definition inc_length :: "(heap, unit) crash_monad"
where
  "inc_length = crash_atom (modify (index_length_update Suc))"

section "Non-Atomic Updates"

text {* Add an entry to the end of the index. *}
definition extend_index :: "nat \<Rightarrow> (heap, unit) crash_monad"
where "extend_index n = doE
        i <- liftE (gets index_length);
        write_index i n;
        inc_length
       odE"

text {* Add a cell, with left and right elements equal.  On termination, this satisfies
  the invariant trivially, but we'll have to prove that it preserves it at every step. *}
definition new_cell :: "nat \<Rightarrow> nat \<Rightarrow> (heap, unit) crash_monad"
where
  "new_cell n x =
    doE
      write_left n x;
      write_right n x;
      extend_index n
    odE"

section "The Correctness Proof"

text {* @{term inc_length} makes the cell pointed to by the next index entry reachable --- this
  cell must therefore be valid. *}
lemma valid_inc:
  "\<lbrace> \<lambda>h. valid_cells (insert (cells h (index h (index_length h))) (lift_cells h)) \<rbrace>
    inc_length
   \<lbrace> \<lambda>_ h. valid_cells (lift_cells h) \<rbrace>, \<lbrace> \<lambda>_ h. valid_cells (lift_cells h) \<rbrace>"
proof -
  txt {* Adding an index entry commutes with lifting the cells. *}
  {
    fix h::heap
    have "{n. n < Suc (index_length h)} = insert (index_length h) {n. n < index_length h}"
      by(auto)
    moreover assume "valid_cells (insert (cells h (index h (index_length h))) (lift_cells h))"
    ultimately have  "valid_cells (lift_cells (index_length_update Suc h))"
      by(simp add:lift_cells_def)
  }
  txt {* If a set of cells is valid, so is a subset. *}
  moreover {
    fix h::heap
    assume "valid_cells (insert (cells h (index h (index_length h))) (lift_cells h))"
    hence "valid_cells (lift_cells h)"
      unfolding valid_cells_def lift_cells_def
      by(auto)
  }
  ultimately show ?thesis
    unfolding inc_length_def
    by(wp add:valid_crash_atom, auto)
qed

text {* Now we generalise to adding an arbitrary location. *}
lemma valid_extend:
  "\<lbrace> \<lambda>h. valid_cells (insert (cells h n) (lift_cells h)) \<rbrace>
    extend_index n
   \<lbrace> \<lambda>_ h. valid_cells (lift_cells h) \<rbrace>, \<lbrace> \<lambda>_ h. valid_cells (lift_cells h) \<rbrace>"
proof -
  txt {* Unpack the validity predicate on the new cell. *}
  have wi_valid: "\<And>i.
        \<lbrace> \<lambda>h. i = index_length h \<and>
              left (cells h n) = right (cells h n) \<and>
              valid_cells (lift_cells h) \<rbrace>
          write_index i n
        \<lbrace> \<lambda>_ h. valid_cells (insert (cells h (index h (index_length h))) (lift_cells h)) \<rbrace>,
        \<lbrace> \<lambda>_ h. valid_cells (lift_cells h) \<rbrace>"
    unfolding write_index_def
    by(wp add:valid_crash_atom,
       simp_all add:valid_cells_def lift_cells_def)

  show ?thesis
    unfolding extend_index_def
    apply(wp add:valid_inc)
    apply(simp)
    apply(wp add:wi_valid)
    apply(simp add:valid_cells_def)
    done
qed

text {* As long as we're not overwriting a cell, the @{term new_cell} preserves the invariant
  both under normal execution, or under a crash at any point. *}
theorem valid_new_cell:
  "\<lbrace> \<lambda>h. n \<notin> occupied h \<and> valid_cells (lift_cells h) \<rbrace>
    new_cell n x
   \<lbrace> \<lambda>_ h. valid_cells (lift_cells h) \<rbrace>,
   \<lbrace> \<lambda>_ h. valid_cells (lift_cells h) \<rbrace>"
proof -
  txt {* @{term write_left} updates the left element, and preserves the invariant. *}
  have wl_valid:
    "\<lbrace> \<lambda>h.  valid_cells (lift_cells h) \<and> n \<notin> occupied h \<rbrace>
      write_left n x
     \<lbrace> \<lambda>_ h. valid_cells (lift_cells h) \<and> n \<notin> occupied h \<and> left (cells h n) = x \<rbrace>,
     \<lbrace> \<lambda>_ h. valid_cells (lift_cells h) \<rbrace>"
    unfolding write_left_def
    by(wp add:valid_crash_atom,
       auto simp:occupied_def lift_cells_def valid_cells_def)

  txt {* @{term write_right} completes the validity predicate on the new cell. *}
  have wr_valid:
    "\<lbrace> \<lambda>h. n \<notin> occupied h \<and> valid_cells (lift_cells h) \<and> left (cells h n) = x\<rbrace>
      write_right n x
     \<lbrace> \<lambda>_ h. valid_cells (insert (cells h n) (lift_cells h)) \<rbrace>,
     \<lbrace> \<lambda>_ h. valid_cells (lift_cells h) \<rbrace>"
    unfolding write_right_def
    by(wp add:valid_crash_atom,
       auto simp:occupied_def lift_cells_def valid_cells_def)

  txt {* Put it all together with the VCG. *}
  show ?thesis
    unfolding new_cell_def
    apply(wp add:valid_extend)
    apply(simp)
    apply(wp add:wr_valid valid_extend)
    apply(simp)
    apply(wp add:wr_valid)
    apply(simp add:conj_comms)
    apply(wp add:wl_valid)
    done
qed

end
