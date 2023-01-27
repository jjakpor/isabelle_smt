theory Core
  imports Main
begin

abbreviation ite:: "bool \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's" where "ite a B C  \<equiv> if a then B else C"

end