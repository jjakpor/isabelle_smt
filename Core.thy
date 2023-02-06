theory Core
  imports Main
begin

definition ite:: "bool \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's" where "ite a B C  \<equiv> if a then B else C"

lemma ite_true[simp]: "(ite True B C) \<Longrightarrow> B"
  apply(simp add: ite_def)
  done

lemma ite_false[simp]: "(ite False B C) \<Longrightarrow> C"
  apply(simp add: ite_def)
  done

end