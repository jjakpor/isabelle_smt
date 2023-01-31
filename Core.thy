theory Core
  imports Main
begin

abbreviation ite:: "bool \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's" where "ite a B C  \<equiv> if a then B else C"

lemma ite_true[simp]: "(ite a B C) \<and> a \<Longrightarrow> B"
  apply(simp)
  done

lemma ite_false[simp]: "(ite a B C) \<and> \<not> a \<Longrightarrow> C"
  apply(simp)
  done

end