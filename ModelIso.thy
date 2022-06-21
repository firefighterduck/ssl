theory ModelIso
imports SSL
begin
lift_definition model_iso :: "model \<Rightarrow> model \<Rightarrow> bool" (infix "\<cong>" 60) is
  "\<lambda>(s,h) (s',h'). (\<exists>f::loc \<Rightarrow> loc. 
    bij_betw f (locs h \<union> ran s) (locs h' \<union> ran s') \<and> 
    bij_betw f (-(locs h \<union> ran s)) (-(locs h' \<union> ran s')) \<and>
    (\<forall>x. s' x = map_option f (s x)) \<and> 
    (Map.graph h' = {(f l, f l') | l l'. h l = Some l'}))" .

abbreviation iso_fun :: "(loc \<Rightarrow> loc) \<Rightarrow> model \<Rightarrow> model \<Rightarrow> bool" where
  "iso_fun f m1 m2 \<equiv> bij_betw f (locs (heap m1) \<union> ran (stack m1)) (locs (heap m2) \<union> ran (stack m2)) \<and> 
  bij_betw f (-(locs (heap m1) \<union> ran (stack m1))) (-(locs (heap m2) \<union> ran (stack m2))) \<and>
  bij f \<and>
  (\<forall>x. stack m2 x = map_option f (stack m1 x)) \<and> 
  (Map.graph (heap m2) = {(f l, f l') | l l'. heap m1 l = Some l'})"

fun iso_fun' :: "(loc \<Rightarrow> loc) \<Rightarrow> (stack\<times>heap) \<Rightarrow> (stack\<times>heap) \<Rightarrow> bool" where
  "iso_fun' f (s,h) (s',h') = (bij_betw f (locs h \<union> ran s) (locs h' \<union> ran s') \<and> 
  bij_betw f (-(locs h \<union> ran s)) (-(locs h' \<union> ran s')) \<and>
  bij f \<and> (\<forall>x. s' x = map_option f (s x)) \<and> (Map.graph h' = (\<lambda>(l,r). (f l, f r))`Map.graph h))"
  
lemma iso_fun_s_bij: "iso_fun f m1 m2 \<Longrightarrow> bij_betw f (ran (stack m1)) (ran (stack m2))"
  by (auto simp: ran_def bij_betw_def) (meson inj_on_Un)

lemma heap_union_graph: "heap_union h1 s h2 = Some h3 \<Longrightarrow> Map.graph h3 = Map.graph h1 \<union> Map.graph h2"
  apply (auto simp: heap_union_def weak_heap_union_def Map.graph_def)
  apply (metis (no_types, lifting) map_add_SomeD option.discI option.inject weak_heap_union_def)
  apply (metis domIff map_add_comm map_add_dom_app_simps(1) option.distinct(1) option.sel weak_heap_union_def)
  by (metis map_add_find_right option.distinct(1) option.sel weak_heap_union_def)

lemma graph_dom_ran: "Map.graph h = (\<lambda>(l, r). (f l, f r)) ` Map.graph h' \<Longrightarrow> dom h = f`dom h' \<and> ran h = f`ran h'"
  by (auto simp: fst_graph_eq_dom[symmetric] snd_graph_ran[symmetric] intro: fst_eqD rev_image_eqI)

lemma iso_heap_union:
assumes "Map.graph h1 = (\<lambda>(l,r). (f l, f r))`Map.graph h2" "bij f"
  "Map.graph h3 = (\<lambda>(l,r). (f l, f r))`Map.graph h4" "ran s' = f`ran s" "heap_union h2 s h4 = Some h5" 
shows "\<exists>h6. heap_union h1 s' h3 = Some h6 \<and> Map.graph h6 = (\<lambda>(l,r). (f l, f r))`Map.graph h5"
proof -
  from assms(5)[unfolded heap_union_def weak_heap_union_def] have 1:
    "dom h2 \<inter> dom h4 = {} \<and> h5=h2++h4 \<and> (dom h2 \<inter> ran h4) \<union> (dom h4 \<inter> ran h2) \<subseteq> ran s"
    by (metis option.distinct(1) option.sel)
  from graph_dom_ran[OF assms(1)] graph_dom_ran[OF assms(3)] have "dom h1 = f`dom h2" 
    "ran h1 = f`ran h2" "dom h3 = f`dom h4" "ran h3 = f`ran h4" by auto
  with 1 assms(2,4) have "dom h1 \<inter> dom h3 = {} \<and> (dom h1 \<inter> ran h3) \<union> (dom h3 \<inter> ran h1) \<subseteq> ran s'"
  apply auto
  apply (metis UNIV_I bij_betw_inv_into_left disjoint_iff domI)
  apply (metis Int_iff UNIV_I bij_betw_inv_into_left domI rev_image_eqI subset_iff)
  by (metis Int_iff UNIV_I bij_betw_inv_into_left domI imageI subset_eq)
  then have "h1 \<uplus>\<^sup>s' h3 \<noteq> None" by (auto simp: heap_union_def weak_heap_union_def)
  then obtain h6 where "h1 \<uplus>\<^sup>s' h3 = Some h6" by auto
  moreover from heap_union_graph[OF this] heap_union_graph[OF assms(5)] assms(1,3)
    have "Map.graph h6 = (\<lambda>(l,r). (f l, f r))`Map.graph h5" by auto
  ultimately show ?thesis by simp
qed  

lemma model_isoE: "m1 \<cong> m2 \<Longrightarrow> \<exists>f. bij_betw f (locs (heap m1) \<union> ran (stack m1)) (locs (heap m2) \<union> ran (stack m2)) \<and> 
  bij_betw f (-(locs (heap m1) \<union> ran (stack m1))) (-(locs (heap m2) \<union> ran (stack m2))) \<and>
  (\<forall>x. stack m2 x = map_option f (stack m1 x)) \<and> 
  (Map.graph (heap m2) = {(f l, f l') | l l'. heap m1 l = Some l'})"
  by transfer' auto

lemma model_isoE': "m1 \<cong> m2 \<Longrightarrow> \<exists>f. iso_fun f m1 m2"
proof -
  assume "m1 \<cong> m2"
  from model_isoE[OF this] obtain f where f:
    "bij_betw f (locs (heap m1) \<union> ran (stack m1)) (locs (heap m2) \<union> ran (stack m2)) \<and> 
    bij_betw f (-(locs (heap m1) \<union> ran (stack m1))) (-(locs (heap m2) \<union> ran (stack m2))) \<and>
    (\<forall>x. stack m2 x = map_option f (stack m1 x)) \<and> 
    (Map.graph (heap m2) = {(f l, f l') | l l'. heap m1 l = Some l'})" by blast
  then have bij_f: "bij f" by auto (metis (no_types, lifting) Compl_disjoint bij_betw_combine 
    boolean_algebra.de_Morgan_disj boolean_algebra.disj_cancel_right)
  with f show ?thesis by blast
qed
  
lemma iso_sym: "m1 \<cong> m2 \<Longrightarrow> m2 \<cong> m1"
proof -
  assume "m1 \<cong> m2"
  from model_isoE'[OF this] obtain f where f: "iso_fun f m1 m2" by blast
  define g where g: "g = inv f"
  have "bij_betw g (locs (heap m2) \<union> ran (stack m2)) (locs (heap m1) \<union> ran (stack m1))"
    unfolding g using f by auto (metis (no_types, lifting) bij_betw_def boolean_algebra.disj_cancel_right 
      image_f_inv_f inj_imp_surj_inv inj_on_Un inv_inv_eq surj_imp_inj_inv)
  moreover have "bij_betw g (-(locs (heap m2) \<union> ran (stack m2))) (-(locs (heap m1) \<union> ran (stack m1)))"
    unfolding g using f by auto (metis (no_types, opaque_lifting) bij_betw_def bij_betw_inv_into_subset g top_greatest)
  moreover have "\<forall>x. stack m1 x = map_option g (stack m2 x)" unfolding g using f 
    by (smt (verit, ccfv_threshold) bij_betw_imp_inj_on inj_imp_surj_inv inv_inv_eq 
      map_option_cong option.map_id option.simps(9) surj_f_inv_f)
  moreover {
    from f have "Map.graph (heap m2) = (\<lambda>(l,l'). (f l, f l')) ` Map.graph (heap m1)"
      unfolding Map.graph_def image_def by auto
    moreover have "heap m2 l = Some l' \<longleftrightarrow> (l,l') \<in> Map.graph (heap m2)" for l l'
      by (auto intro: Map.in_graphI Map.in_graphD)
    ultimately have "Map.graph (heap m1) = {(g l, g l') | l l'. heap m2 l = Some l'}"
    unfolding g using f apply auto using bij_inv_eq_iff in_graphD mem_Collect_eq apply fastforce
      by (metis bij_inv_eq_iff)    
  }
  ultimately show ?thesis apply transfer' by auto
qed
    
lemma iso_stack_dom: "m1 \<cong> m2 \<Longrightarrow> dom (stack m1) = dom (stack m2)"
proof -
  assume assm: "m1 \<cong> m2"
  from model_isoE[OF this] show ?thesis by auto
qed

lemma iso_heap: "m1 \<cong> m2 \<Longrightarrow> card (dom (heap m1)) = card (dom (heap m2)) 
  \<and> card (ran (heap m1)) = card (ran (heap m2))"
proof -
  assume assm: "m1 \<cong> m2"
  from model_isoE'[OF this] obtain f where f: "iso_fun f m1 m2" by blast
  then have m_graph: "Map.graph (heap m2) = (\<lambda>(l,r). (f l, f r)) ` Map.graph (heap m1)"
    unfolding Map.graph_def by auto  
  then have "fst ` Map.graph (heap m2) = f ` (fst ` Map.graph (heap m1))" by force
  from this[unfolded fst_graph_eq_dom] have "card (dom (heap m1)) = card (dom (heap m2))"
    by (smt (verit, del_insts) UnI1 bij_betw_iff_bijections card_image f inj_on_def locs_def)
  moreover {
    from m_graph have "snd ` Map.graph (heap m2) = f ` (snd ` Map.graph (heap m1))" by force
    moreover have "inj_on f (ran (heap m1))" using f apply auto
      using bij_betw_imp_inj_on inj_on_def locs_def by fastforce
    ultimately have "card (ran (heap m1)) = card (ran (heap m2))" 
      unfolding snd_graph_ran using card_image by metis
   }
  ultimately show ?thesis by simp  
qed

lemma iso_heap_emp: "m1 \<cong> m2 \<Longrightarrow> (heap m1 = Map.empty) \<longleftrightarrow> (heap m2 = Map.empty)"
proof -
  assume "m1 \<cong> m2"
  from iso_heap[OF this] have "card (dom (heap m1)) = card (dom (heap m2))" by simp
  then have "card (dom (heap m1)) = 0 \<longleftrightarrow> card (dom (heap m2)) = 0" by simp
  moreover {
    fix x :: heap
    assume "finite (dom x)"
    then have "card (dom x) = 0 \<longleftrightarrow> x = Map.empty" by auto
    }
  moreover have "finite (dom (heap x))" for x by transfer auto
  ultimately show ?thesis by simp
qed

(* lemma list_segment_iso: 
  "\<lbrakk>list_segment n h1 l1 l2; iso_fun' f (s,h1) (s',h2)\<rbrakk> \<Longrightarrow> list_segment n h2 (f l1) (f l2)"
proof (induction n h1 l1 l2 rule: list_segment.induct)
  case (1 uu uv uw)
  then show ?case by auto
next
  case (2 h1 l1 l2)
  then have h1: "h1 = [l1\<mapsto>l2]" by auto
  from 2(2) have "Map.graph h2 = (\<lambda>(l,r). (f l,f r))`Map.graph h1" by simp
  from graph_dom_ran[OF this] have "dom h2 = f`dom h1" "ran h2 = f`ran h1" by simp_all
  with h1 have "h2 = [f l1 \<mapsto> f l2]" apply auto
    by (metis dom_eq_singleton_conv insertCI ran_map_upd singleton_iff)
  then show ?case by auto
next
  case (3 n h1 l1 l2)
  then obtain h' l1' where h': "h1=h'++[l1\<mapsto>l1']" "list_segment (Suc n) h' l1' l2" "l1 \<notin> dom h'" by auto
  define h'' where h'': "h'' = h2(f l1 := None)"
  with h'(3) have doms: "dom h'' \<inter> dom [f l1 \<mapsto> f l1'] = {}" "dom h' \<inter> dom [l1 \<mapsto>l1'] = {}" by auto
  from h'(1) have "h1 l1 = Some l1'" by simp
  with 3(3) have "h2 (f l1) = Some ( f l1')"
    by (auto simp: Map.graph_def)
  with h'' have h2: "h2=h''++[f l1 \<mapsto> f l1']" by auto  
  from 3(3)[simplified, unfolded this h'(1)] have "Map.graph h'' \<union> {(f l1,f l1')} = (\<lambda>(l,r). (f l,f r))`(Map.graph h' \<union> {(l1,l1')})"
    unfolding graph_map_add[OF doms(1)] graph_map_add[OF doms(2)] by auto
  with doms have h'_h''_graph: "Map.graph h'' = (\<lambda>(l,r). (f l,f r))`Map.graph h'"
    apply auto apply (metis in_graphD insert_iff option.distinct(1))
    by (metis (mono_tags, lifting) UNIV_I 3(3)[simplified, unfolded h2 h'(1)] 
      bij_betw_inv_into_left domI domIff fst_eqD in_graphD insert_iff pair_imageI)
  from 3(3) have "ran s' = f`ran s" by (auto simp: ran_def)
  with 3(3) have s_bij: "bij_betw f (ran s) (ran s')" by (auto simp: bij_betw_def inj_on_def)
  with 3(3) have h_bij: "bij_betw f (locs h1) (locs h2)" apply auto
    by (simp add: bij_betw_def graph_dom_ran image_Un inj_on_Un locs_def)  
  from h'(1,3) h'' h2 have "locs h' \<union> {l1,l1'} = locs h1" "locs h'' \<union> {f l1,f l1'} = locs h2"
    apply (auto simp: locs_def)
    apply (metis \<open>h2 (f l1) = Some (f l1')\<close> ranI)
    apply (metis UnI2 doms(1) h2 inf_commute map_add_comm ran_map_add)
    by (metis fun_upd_idem_iff insert_iff ran_map_upd)
  with h_bij have union_bij: "bij_betw f (locs h' \<union> {l1,l1'}) (locs h'' \<union> {f l1, f l1'})" by simp
  with 3(3) graph_dom_ran[OF h'_h''_graph] have "bij_betw f (dom h') (dom h'')" "bij_betw f (ran h') (ran h'')"
    by (auto simp: bij_betw_def inj_on_def)
  then have "bij_betw f (locs h') (locs h'')" apply (auto simp: locs_def)
    by (metis union_bij bij_betw_def image_Un inj_on_Un locs_def)
  with s_bij have "bij_betw f (locs h' \<union> ran s) (locs h'' \<union> ran s')" apply (auto simp: bij_betw_def)
    by (metis 3(3)[simplified, unfolded h2 h'(1)] bij_is_inj injD inj_onI) 
  moreover with 3(3)[simplified, unfolded h2 h'(1)] have "bij_betw f (-(locs h' \<union> ran s)) (-(locs h'' \<union> ran s'))"
    by auto (metis bij_betw_def bij_image_Compl_eq boolean_algebra.de_Morgan_disj boolean_algebra.disj_one_right inj_on_Un)  
  ultimately have "bij_betw f (locs h' \<union> ran s) (locs h'' \<union> ran s') \<and> 
    bij_betw f (-(locs h' \<union> ran s)) (-(locs h'' \<union> ran s')) \<and>
    bij f \<and> (\<forall>x. s' x = map_option f (s x)) \<and> (Map.graph h'' = (\<lambda>(l,r). (f l, f r))`Map.graph h')"
    using 3(3) h'_h''_graph by auto
  then have "iso_fun' f (s,h') (s',h'')" by simp
  from doms 3(1)[OF h'(2) this] have "list_segment h2 (f l1) (f l2) (Suc (Suc n))"
    by (auto simp: h2)
  then show ?case .
qed *)

lemma iso_split: "\<lbrakk>m1\<cong>m2; heap m1=h; stack m1 = s; stack m2 = s'; heap m2=h'; h1 \<uplus>\<^sup>s h2=Some h\<rbrakk> \<Longrightarrow>
  \<exists>h1' h2'. heap_union h1' s' h2'=Some h' \<and> Abs_model (s,h1) \<cong> Abs_model (s',h1') \<and> Abs_model (s,h2) \<cong> Abs_model (s',h2')"
proof -
  assume assms: "m1\<cong>m2" "heap m1=h" "stack m1 = s" "stack m2 = s'" "heap m2=h'" "h1 \<uplus>\<^sup>s h2=Some h"
  from model_isoE'[OF this(1)] assms obtain f where f:
    "bij_betw f (locs h \<union> ran s) (locs h' \<union> ran s') \<and>  bij_betw f (-(locs h \<union> ran s)) (-(locs h' \<union> ran s')) \<and>
    bij f \<and> (\<forall>x. s' x = map_option f (s x)) \<and> 
    (Map.graph h' = {(f l, f l') | l l'. h l = Some l'})" by blast
  define h1' h2' where h12': "h1' = h' |` (f ` dom h1)" "h2' = h' |` (f ` dom h2)"
  from f have m_graph: "Map.graph h' = (\<lambda>(l,r). (f l, f r)) ` Map.graph h"
    unfolding Map.graph_def by auto    
  then have "fst ` Map.graph h' = f ` (fst ` Map.graph h)" by force
  then have "dom h' = f`dom h" using assms by (simp add: fst_graph_eq_dom)
  with assms have "dom h' = f`(dom h1 \<union> dom h2)" 
    apply (auto simp: heap_union_def weak_heap_union_def)
    apply (metis domI dom_map_add imageI not_Some_eq option.inject sup.commute weak_heap_union_def)
    apply (metis UnCI domI dom_map_add imageI option.distinct(1) option.inject weak_heap_union_def)
    by (metis Un_iff domI dom_map_add option.discI option.inject rev_image_eqI weak_heap_union_def)
  then have dom_h': "dom h' = (f`dom h1) \<union> (f`dom h2)" by auto
  from assms f have inter_emp: "f`dom h1 \<inter> f`dom h2 = {}" apply (auto simp: heap_union_def weak_heap_union_def)
    by (smt (verit, ccfv_SIG) ComplD Compl_Un Compl_disjoint Compl_partition2 IntI UNIV_I bij_betw_inv_into_left 
      boolean_algebra_class.boolean_algebra.double_compl domI not_None_eq weak_heap_union_def)
  then have inter_emp': "dom (h' |` (f ` dom h1)) \<inter> dom (h' |` (f ` dom h2)) = {}" by auto
  from dom_h' have "Map.graph (h' |` (f`dom h1)) \<union> Map.graph (h' |` (f`dom h2)) = Map.graph h'"
    apply (auto intro: graph_restrictD in_graphI)
    by (metis UnE fst_conv graph_domD in_graphD in_graphI restrict_in)
  with graph_map_add[OF inter_emp'] have "Map.graph (h'|`(f`dom h1)++h'|`(f`dom h2)) = Map.graph h'" 
    by simp
  moreover have "Map.graph x = Map.graph y \<Longrightarrow> x = y" for x y :: heap 
    by (metis (no_types, opaque_lifting) ext in_graphD in_graphI option.collapse)
  ultimately have h'_plus: "(h'|`(f`dom h1)++h'|`(f`dom h2)) = h'" by simp
  with h12' inter_emp' have h_w_union: "Some h' = h1' ++ h2'" by (auto simp: weak_heap_union_def)
  from f have "ran s' = {y | x y. map_option f (s x) = Some y}" by (auto simp: ran_def)
  then have ran_s': "ran s' = f`(ran s)" by (auto simp: ran_def)
  from assms(6) have union: "(dom h1 \<inter> ran h2) \<union> (dom h2 \<inter> ran h1) \<subseteq> ran s" apply (auto simp: heap_union_def)
    by (metis IntI domIff option.distinct(1) subset_iff)+
  from h12' dom_h' have dom': "dom h1'= (f`dom h1)" "dom h2' = (f`dom h2)" by auto
  from m_graph have "h l = Some l' \<longleftrightarrow> h' (f l) = Some (f l')" for l l'
    by (auto simp: Map.graph_def) (smt (verit, del_insts) bij_betw_imp_inj_on f graph_def 
    inj_imp_surj_inv inv_inv_eq mem_Collect_eq prod.simps(1) surj_f_inv_f)
  moreover from m_graph have "h l = None \<longleftrightarrow> h' (f l) = None" for l apply (auto simp: Map.graph_def)
    apply (smt (verit) \<open>fst ` Map.graph h' = f ` fst ` Map.graph h\<close> bij_betw_imp_inj_on domIff f fst_graph_eq_dom imageE inj_imp_surj_inv inv_inv_eq surj_f_inv_f)
    by (metis \<open>dom h' = f ` dom h\<close> domIff rev_image_eqI)
  ultimately have "h' (f l) = map_option f (h l)" for l
    by (metis (mono_tags, opaque_lifting) None_eq_map_option_iff option.exhaust_sel option.simps(9))
  then have "h' (f l) = map_option f (if l \<in> dom h1 then h1 l else h2 l)" for l
    using assms(6) apply (auto simp: heap_union_def weak_heap_union_def)
    apply (smt (verit, del_insts) map_add_comm map_add_find_right option.distinct(1) option.inject weak_heap_union_def)
    by (smt (verit, ccfv_SIG) map_add_SomeD map_add_find_right option.collapse option.inject option.simps(3) weak_heap_union_def)
  with h12' have maps: "h1' (f l) = map_option f (h1 l)" "h2' (f l) = map_option f (h2 l)" for l apply auto  
    apply (metis (full_types, opaque_lifting) None_eq_map_option_iff dom' disjoint_iff domIff imageI inter_emp restrict_in)
    by (metis (full_types) disjoint_iff domIff imageI inter_emp option.map_disc_iff restrict_in restrict_out)
  then have "ran h1' = f`ran h1" "ran h2' = f`ran h2" apply (auto simp: ran_map_option[symmetric])
    by (smt (verit, ccfv_SIG) bij_inv_eq_iff f mem_Collect_eq ran_def)+
  with dom' ran_s' union have "(dom h1' \<inter> ran h2') \<union> (dom h2' \<inter> ran h1') \<subseteq> ran s'"
    by auto (smt (verit, ccfv_SIG) Int_iff bij_betw_imp_inj_on domIff f image_eqI inj_imp_surj_inv 
    inv_inv_eq option.distinct(1) subset_iff surj_f_inv_f)+
  with h_w_union have heap_union: "Some h' = heap_union h1' s' h2'" by (auto simp: heap_union_def)
  note abs = heap_union_model[OF assms(2,3) assms(6)[symmetric]] heap_union_model[OF assms(5,4) heap_union]
    heap_union_model[OF assms(2,3) assms(6)[symmetric, THEN heap_union_sym_impl]]
    heap_union_model[OF assms(5,4) heap_union[THEN heap_union_sym_impl]]
  { 
    from f have "bij_betw f (locs h1 \<union> ran s) (locs h1' \<union> ran s')" apply auto
      by (metis (no_types, lifting) Un_commute \<open>ran h1' = f ` ran h1\<close> bij_betw_def bij_betw_imp_inj_on boolean_algebra.disj_cancel_left dom'(1) image_Un inj_on_Un locs_def ran_s')
    moreover from this f have "bij_betw f (- locs h1 \<inter> - ran s) (- locs h1' \<inter> - ran s')"
      by auto (metis (no_types, lifting) bij_betw_def bij_image_Compl_eq boolean_algebra.de_Morgan_disj boolean_algebra.disj_one_right inj_on_Un)
    moreover from f have "\<forall>x. s' x = map_option f (s x)" by simp
    moreover from maps have "Map.graph h1' = {(f l, f l') |l l'. h1 l = Some l'}"
      by (auto simp: in_graphI) (metis dom'(1) fst_conv graph_domD image_iff in_graphD map_option_eq_Some)
    ultimately have "Abs_model (s, h1) \<cong> Abs_model (s', h1')" 
      by (auto simp: model_iso.rep_eq Abs_model_inverse[OF abs(1)] Abs_model_inverse[OF abs(2)])
  }
  moreover { 
    from f have "bij_betw f (locs h2 \<union> ran s) (locs h2' \<union> ran s')" apply auto
      by (metis (no_types, lifting) Un_commute \<open>ran h2' = f ` ran h2\<close> bij_betw_def bij_betw_imp_inj_on boolean_algebra.disj_cancel_left dom'(2) image_Un inj_on_Un locs_def ran_s')
    moreover from this f have "bij_betw f (- locs h2 \<inter> - ran s) (- locs h2' \<inter> - ran s')"
      by auto (metis (no_types, lifting) bij_betw_def bij_image_Compl_eq boolean_algebra.de_Morgan_disj boolean_algebra.disj_one_right inj_on_Un)
    moreover from f have "\<forall>x. s' x = map_option f (s x)" by simp
    moreover from maps have "Map.graph h2' = {(f l, f l') |l l'. h2 l = Some l'}" apply (auto simp: in_graphI) 
      by (smt (verit) Pair_inject dom'(2) fst_conv graph_def graph_domD image_iff map_option_eq_Some mem_Collect_eq)
    ultimately have "Abs_model (s, h2) \<cong> Abs_model (s', h2')" 
      by (auto simp: model_iso.rep_eq Abs_model_inverse[OF abs(3)] Abs_model_inverse[OF abs(4)])
  }
  ultimately show ?thesis using heap_union by auto
qed
  
theorem iso_equivalent: "m1 \<cong> m2 \<Longrightarrow> m1 \<Turnstile> P \<Longrightarrow> m2 \<Turnstile> P"
proof (induction P arbitrary: m1 m2)
  case Emp
  with iso_heap_emp[OF this(1)] this(2) show ?case by transfer' auto
next
  case (PointsTo x y)
  then obtain x' y' where h1: "stack m1 x = Some x' \<and> stack m1 y = Some y' \<and> heap m1 = [x'\<mapsto>y']"
    by transfer' auto
  from model_isoE'[OF PointsTo(1)] obtain f where f: "iso_fun f m1 m2" by blast
  with h1 have "Map.graph (heap m2) = {(f x', f y')}" by auto
  then have "heap m2 = [f x' \<mapsto> f y']" by (metis (full_types) dom_eq_singleton_conv fst_graph_eq_dom 
    fun_upd_idem graph_empty graph_map_upd in_graphD insertI1)
  moreover have "stack m2 x = Some (f x') \<and> stack m2 y = Some (f y')" using f apply auto 
    using h1 by blast+
  ultimately show ?case by transfer auto
next
  case (LS x)
  (* obtain y z where x: "x=(y,z)" by force
  obtain s h s' h' where m1: "heap m1 = h" "stack m1 = s" and m2: "heap m2 = h'" "stack m2 = s'" 
    by auto
  then have m12: "Rep_model m1 = (s,h)" "Rep_model m2 = (s',h')" by (transfer, auto)+
  with x LS(2) have "satisfies (s,h) (LS (y,z))" by transfer' auto
  then obtain ly lz where ls_sat: "s y = Some ly" "s z = Some lz" 
    "((dom h = {} \<and> ly=lz) \<or> (\<exists>n. list_segment h ly lz n))" (is "?emp_ls \<or> ?seg") by auto
  from model_isoE'[OF LS(1)] obtain f where f: "iso_fun f m1 m2" by blast
  with ls_sat m1 m2 have s'_y_z: "s' y = Some (f ly)" "s' z = Some (f lz)" by auto
  {
    from f iso_heap_emp[OF LS.prems(1)] m1 m2 have "?emp_ls \<Longrightarrow> dom h' = {} \<and> f ly = f lz" by auto
    with s'_y_z have "?emp_ls \<Longrightarrow> satisfies (s',h') (LS (y,z))" by auto
    with m12(2) x have "?emp_ls \<Longrightarrow> m2 \<Turnstile> LS x" by (auto simp: satisfies_model.rep_eq)
  }
  moreover {
    assume ?seg
    then obtain n where n: "list_segment h ly lz n" by blast
    from f m1 m2 have "iso_fun' f (s,h) (s',h')" by (auto simp: Map.graph_def)
    from list_segment_iso[OF n this] have "(dom h' = {} \<and> f ly=f lz) \<or> (\<exists>n. list_segment h' (f ly) (f lz) n)"
      by auto
    with s'_y_z have "satisfies (s',h') (LS (y,z))" by auto
    with m12(2) x have "m2 \<Turnstile> LS x" by (auto simp: satisfies_model.rep_eq)
  }
  ultimately show ?case using ls_sat(3) by auto *) show ?case sorry
next
  case (Eq x1 x2)
  with iso_heap_emp[OF this(1)] show ?case by transfer auto
next
  case (NEq x1 x2)
  with iso_heap_emp[OF this(1)] model_isoE'[OF this(1)] show ?case 
    by transfer (auto, metis bij_inv_eq_iff)
next
  case (SepConj P1 P2)
  obtain s h s' h' where m1: "heap m1 = h" "stack m1 = s" and m2: "heap m2 = h'" "stack m2 = s'" 
    by auto
  with SepConj(4) obtain h1 h2 where h12: "h1 \<uplus>\<^sup>s h2 = Some h" "Abs_model (s,h1) \<Turnstile> P1" 
    "Abs_model (s,h2) \<Turnstile> P2" apply transfer apply auto by (smt (verit, ccfv_threshold) Abs_model_inverse 
      UnI1 UnI2 domD dom_map_add finite_Un heap_union_def mem_Collect_eq option.distinct(1) option.inject 
      satisfies_model.rep_eq weak_heap_union_def)
  from model_isoE'[OF SepConj(3)] obtain f where f: "iso_fun f m1 m2" by blast
  from iso_split[OF SepConj(3) m1 m2(2,1) h12(1)] obtain h1' h2' where h12': "Some h'= h1' \<uplus>\<^sup>s' h2'"
     "Abs_model (s, h1) \<cong> Abs_model (s', h1')" "Abs_model (s, h2) \<cong> Abs_model (s', h2')" by force
  note abs = heap_union_model[OF m2 h12'(1)] heap_union_model[OF m2 h12'(1)[THEN heap_union_sym_impl]]
  from m2 have "Rep_model m2 = (s',h')" by transfer auto   
  with SepConj(1)[OF h12'(2) h12(2)] SepConj(2)[OF h12'(3) h12(3)] h12'(1) have "m2 \<Turnstile> P1 \<^emph> P2" 
    by (auto simp: satisfies_model.rep_eq Abs_model_inverse[OF abs(1)] Abs_model_inverse[OF abs(2)])
  then show ?case .
next
  case (Septraction P1 P2)
  obtain s h s' h' where m1: "heap m1 = h" "stack m1 = s" and m2: "heap m2 = h'" "stack m2 = s'" 
    by auto
  then have m12: "Rep_model m1 = (s,h)" "Rep_model m2 = (s',h')" by (transfer, auto)+
  with Septraction(4) have "satisfies (s,h) (P1 -\<otimes> P2)" by transfer auto
  \<comment> \<open>Obtain the h0\<close>
  with m12 obtain h0 h1 l where h12: "h \<uplus>\<^sup>s h0 = Some h1" "satisfies (s,h0) P1" "satisfies (s,h1) P2" 
    "finite (dom h0)" "s Nil = Some l" "l \<notin> dom h0"
    by auto
  with m12 have "(s,h0) \<in> {(s, h) |s h. finite (dom s) \<and> finite (dom h) \<and> (\<exists>l. s var.Nil = Some l \<and> l \<notin> dom h)}"
    by transfer auto
  note abs = heap_union_model'[OF m1 h12(5) h12(1)[symmetric] h12(6,4)] this
  from model_isoE'[OF Septraction(3)] obtain f where f: "iso_fun f m1 m2" by blast
  then have f_bij: "bij f" by simp
  from f have h_h'_graph: "Map.graph h' = (\<lambda>(l,r). (f l, f r))`Map.graph h" by (auto simp: Map.graph_def m1 m2)
  from f have s_s'_ran: "ran s' = f`ran s" by (auto simp: ran_def m1 m2)
  from h12(5) f m1 m2 have s'_nil: "s' Nil = Some (f l)" by simp
  \<comment> \<open>Define the isomorphic heap h0' to h0.\<close>
  define h0' where "h0' \<equiv> \<lambda>l. map_option f (h0 (inv f l))"
  with f_bij have h0'_graph: "Map.graph h0' = {(f l, f l') | l l'. h0 l = Some l'}"
    apply (auto simp: Map.graph_def bij_betw_inv_into_left)
    by (metis bij_inv_eq_iff)
  with h0'_def have h0'_dom_ran: "dom h0' = f`dom h0" "ran h0' = f`ran h0" apply (auto simp: Map.graph_def ran_def)
    apply fastforce+ by (metis bij_inv_eq_iff f_bij)
  with h12(4,5,6) have h0'_heap: "finite (dom h0')" "f l \<notin> dom h0'" 
    by auto (metis bij_inv_eq_iff f_bij option.simps(3))  
  with m2 s'_nil have abs_h0': "(s',h0') \<in> {(s, h) |s h. finite (dom s) \<and> finite (dom h) \<and> (\<exists>l. s var.Nil = Some l \<and> l \<notin> dom h)}"
    by transfer auto
  from h0'_dom_ran f_bij have h0_h0'_bij: "bij_betw f (locs h0) (locs h0')"
    by (auto simp: locs_def bij_betw_def inj_on_def) 
  with iso_fun_s_bij[OF f] m1 m2 have "bij_betw f (locs h0 \<union> ran s) (locs h0' \<union> ran s')"
    by auto (metis h0_h0'_bij bij_betw_def boolean_algebra.disj_one_left f_bij image_Un inj_on_Un m2(2))  
  moreover with f_bij have "bij_betw f (-(locs h0 \<union> ran s)) (-(locs h0' \<union> ran s'))"
    by (metis Compl_partition2 bij_betw_def bij_image_Compl_eq inj_on_Un)
  ultimately have "bij_betw f (locs h0 \<union> ran s) (locs h0' \<union> ran s') \<and>
    bij_betw f (- locs h0 \<inter> - ran s) (- locs h0' \<inter> - ran s') \<and>
    (\<forall>x. s' x = map_option f (s x)) \<and> Map.graph h0' = {(f l, f l') |l l'. h0 l = Some l'}"
    using f[unfolded m1 m2] h0'_graph by auto
  then have h0_iso_h0': "Abs_model (s,h0) \<cong> Abs_model (s',h0')"
    by (auto simp: model_iso.rep_eq Abs_model_inverse[OF abs_h0'] Abs_model_inverse[OF abs(2)])
  from h0'_graph have "Map.graph h0' = (\<lambda>(l,r). (f l, f r))`Map.graph h0" by (auto simp: Map.graph_def)
  from iso_heap_union[OF this f_bij h_h'_graph s_s'_ran h12(1)[symmetric, THEN heap_union_sym_impl, symmetric]]
  \<comment> \<open>Obtain the isomorphic heap h3 for h1\<close>
  obtain h3 where h3: "h0' \<uplus>\<^sup>s' h' = Some h3" "Map.graph h3 = (\<lambda>(l, r). (f l, f r)) ` Map.graph h1" 
    by blast
  with h0'_heap m12 s'_nil have h3_heap: "finite (dom h3) \<and> f l \<notin> dom h3" apply transfer apply auto
    apply (metis finite_UnI finite_graph_iff_finite_dom heap_union_graph) 
    by (metis UnE domIff fst_graph_eq_dom heap_union_graph image_Un option.distinct(1))
  with m2 s'_nil have abs_h3: "(s',h3) \<in> {(s, h) |s h. finite (dom s) \<and> finite (dom h) \<and> (\<exists>l. s var.Nil = Some l \<and> l \<notin> dom h)}"
    by transfer auto
  from graph_dom_ran[OF h3(2)] f_bij have "bij_betw f (locs h1) (locs h3)"
    by (auto simp: locs_def bij_betw_def inj_on_def)
  with iso_fun_s_bij[OF f] m1 m2 have "bij_betw f (locs h1 \<union> ran s) (locs h3 \<union> ran s')"
    by auto (metis bij_betw_def boolean_algebra.disj_one_left f_bij image_Un inj_on_Un m2(2))  
  moreover with f_bij have "bij_betw f (-(locs h1 \<union> ran s)) (-(locs h3 \<union> ran s'))"
    by (metis Compl_partition2 bij_betw_def bij_image_Compl_eq inj_on_Un)
  ultimately have "bij_betw f (locs h1 \<union> ran s) (locs h3 \<union> ran s') \<and>
    bij_betw f (- locs h1 \<inter> - ran s) (- locs h3 \<inter> - ran s') \<and>
    (\<forall>x. s' x = map_option f (s x)) \<and> Map.graph h3 = {(f l, f l') |l l'. h1 l = Some l'}"
    using f[unfolded m1 m2] h3(2) by (auto simp: Map.graph_def)
  then have h1_iso_h3: "Abs_model (s,h1) \<cong> Abs_model (s',h3)"
    by (auto simp: model_iso.rep_eq Abs_model_inverse[OF abs_h3] Abs_model_inverse[OF abs(1)])
  \<comment> \<open>Apply the induction hypothesis.\<close>
  from h12(2,3) have "Abs_model (s,h0) \<Turnstile> P1" "Abs_model (s,h1) \<Turnstile> P2"
    by (auto simp: satisfies_model.rep_eq Abs_model_inverse[OF abs(1)] Abs_model_inverse[OF abs(2)])
  from Septraction(1)[OF h0_iso_h0' this(1)] Septraction(2)[OF h1_iso_h3 this(2)] s'_nil h0'_heap h3(1) have 
    "finite (dom h0') \<and> s' Nil = Some (f l) \<and> f l \<notin> dom h0' \<and> satisfies (s', h0') P1 \<and> h' \<uplus>\<^sup>s' h0' = Some h3 \<and> satisfies (s', h3) P2"
    by (auto simp: satisfies_model.rep_eq Abs_model_inverse[OF abs_h3] m12 Abs_model_inverse[OF abs_h0']
      heap_union_sym)
    then show ?case by (auto simp: satisfies_model.rep_eq Abs_model_inverse[OF abs_h3] m12 Abs_model_inverse[OF abs_h0'])
next
  case (Conj P1 P2)
  then have "m1 \<Turnstile> P1" "m1 \<Turnstile> P2" by (transfer',auto)+
  from Conj(1)[OF Conj(3) this(1)] Conj(2)[OF Conj(3) this(2)] show ?case
    by transfer auto
next
  case (Disj P1 P2)
  then have "m1 \<Turnstile> P1 \<or> m1 \<Turnstile> P2" by transfer' auto
  with Disj(1)[OF Disj(3)] Disj(2)[OF Disj(3)] show ?case
    by transfer' auto
next
  case (Neg P)
  then have "\<not> (m1 \<Turnstile> P)" by transfer auto
  with Neg(1)[OF iso_sym[OF Neg(2)]] show ?case by transfer' auto
qed
end