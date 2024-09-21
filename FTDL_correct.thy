theory FTDL_correct
  imports FTDL
begin

fun heb_expand::"behavior \<Rightarrow> entity \<Rightarrow> entity"where"
heb_expand x (static y) = static (fst(snd(x)) y)"|"
heb_expand x (dynamic y) = dynamic (connect ((fst(snd(x))) (fst(y))) (snd(y)))"
(*fst(snd(x)) (fst(y)))*)
definition is_acessing ::"entity \<Rightarrow> bool"where"
is_acessing x = (if get_entity_visit_bit x = 1 then True else False)"
definition is_activating::"entity \<Rightarrow> bool"where"
is_activating x =(if get_entity_activate_bit x = 1 then True else False)"


definition no_eq_task::"task \<Rightarrow> task \<Rightarrow> bool"where"
no_eq_task ti tj = ((ti \<noteq> tj)\<and>((fst(ti)) \<noteq> [])\<and>((fst(tj)) \<noteq> [])\<and>((fst(tj)) \<noteq> (fst(ti))))"
definition no_eq_beh::"behavior \<Rightarrow> behavior \<Rightarrow> bool"where"
no_eq_beh beh1 beh2 = ((beh1 \<noteq> beh2)\<and>(fst(beh1) \<noteq> fst(beh2)))"

fun act_state::"entity list \<Rightarrow> bool"where"
act_state [] = True"|"
act_state (e#es) = (if (get_entity_activate_bit e = 0)\<or>(get_entity_activate_bit e = 1) then act_state es else False)"

fun en_list ::"entity list \<Rightarrow> entity_name list"where"
en_list [] = []"|"
en_list (e#es) = get_entity_name e # en_list es"

definition name_uni ::"entity list \<Rightarrow> bool "where"
name_uni es = (distinct (en_list es))"

definition prop_DVE::"entity list \<Rightarrow> bool"where"
prop_DVE es = (distinct (en_list es)\<and>(act_state es))"

fun step_seq ::"task_body \<Rightarrow> bool"where"
step_seq [] = True"|"
step_seq [t1] = (get_beh_step (snd(t1)) = 1)"|"
step_seq (t1#t2#ts) = 
      (if get_beh_step (snd(t1)) = 1 
        then (if get_beh_step (snd(t1)) + 1 = get_beh_step (snd(t2)) 
               then step_seq (t2#ts) 
                else False)
          else False)"
definition prop_T::"task \<Rightarrow> bool"where"
prop_T t = step_seq (get_task_body t)"

fun get_entity_act::"entity \<Rightarrow> is_activated"where"
get_entity_act (static e) = (fst(snd(snd(e))))"|"
get_entity_act (dynamic e) = (fst(snd(snd(fst(e)))))"
fun init_act::"entity \<Rightarrow> bool"where"
init_act e = ((fst(get_entity_act e) = '''')\<and>((snd(get_entity_act e) = 0)))"


fun get_entity_vis::"entity \<Rightarrow> is_activated"where"
get_entity_vis (static e) = (snd(snd(snd(e))))"|"
get_entity_vis (dynamic e) = (snd(snd(snd(fst(e)))))"
definition init_vis::"entity \<Rightarrow> bool"where"
init_vis e = ((fst(get_entity_vis e) = '''')\<and>((snd(get_entity_vis e) = 0)))"

definition prop_E::"entity \<Rightarrow> bool"where"
prop_E e = (init_act e \<and> init_vis e)"



(*------------behavior correct---------------*)
definition contain_beh ::" entity \<Rightarrow> behavior \<Rightarrow> bool"where"
contain_beh e beh = (ent_cont_beh beh (get_ent_behlist e))"

lemma connect:"connect x y = (x,y)"
  apply (simp add: FTDL.connect_def)
  done
lemma beh_body:"beh_body x y = fst(snd(x)) y"
  apply (simp add: beh_body_def)
  done

theorem beh_Correct:"entity_behavior beh e = heb_expand beh e"
  apply (induction e)
   apply simp
  using heb_expand.simps beh_body 
   apply auto
  done

theorem entity_Auth:"contain_beh e beh \<Longrightarrow> has_auth e beh"
  apply (simp add: contain_beh_def)
  apply (induction e)
   apply auto
  using ent_cont_beh.elims(2) by fastforce




(*-------------activate entity correct--------------*)

lemma act_bit:"change_bit1 x = 1 "
  apply auto
  apply (simp add: change_bit1_def)
  done

lemma act_entity:"get_activate_bit (act_entity x) = 1"
  apply auto
  apply (induction x)
   apply simp prefer 2
   apply simp+
  using act_bit.cases  apply auto
  using connect  apply (simp add: act_bit)
  apply (simp add: change_bit1_def)
  done

fun entity_cont::"entity \<Rightarrow> entity list \<Rightarrow> bool"where"
entity_cont x [] = False"|"
entity_cont x (e#es) = (\<exists>ej\<in> set(e#es). get_entity_name x = get_entity_name ej)"
(*entity_cont x (e#es) = (if (get_entity_name (x) = get_entity_name (e)) then True else entity_cont x es)*)
fun get_entity::"entity_name \<Rightarrow> entity list \<Rightarrow> entity"where"
get_entity en [] = hd[]"|"
get_entity en (e#es) = (if (en = get_entity_name (e)) then e else get_entity en es)"
fun entity_name_uni::"entity list \<Rightarrow> bool"where"
entity_name_uni [] = True"|"
entity_name_uni (e#es) = (\<forall>x \<in> set (e#es).  \<forall>y \<in> set (e#es). (get_entity_name x \<noteq> get_entity_name y))"

lemma act_ent:
  assumes "act_cond en ei"
          "\<exists>ej\<in> set(e#es). get_entity_name ei = get_entity_name ej"
          "\<forall>x \<in> set (e#es).  \<forall>y \<in> set (e#es). (get_entity_name x \<noteq> get_entity_name y)"
  shows   "get_activate_bit (get_entity en (entity_activation en (e#es))) = 1"
  using assms(1) assms(2)  apply auto
  apply (induction e)
  apply (simp add: act_entity)
  using act_entity apply simp
   apply auto
   apply (simp add: change_bit1_def)
  apply (simp add: change_bit1_def)
  using connect apply force
  using entity_cont.simps get_entity.simps apply auto
  using assms(3) apply simp+
  done

lemma act_name:"get_entity_name e = get_entity_name (act_entity e)"
  apply (induction e)
   apply auto
  apply (simp add: change_bit1_def)
  using connect by auto



lemma entity_activated:"act_state es \<Longrightarrow>
    act_condlist en es \<Longrightarrow> get_activate_bit (get_entity en (entity_activation en es)) = Suc 0"
  apply (induction es)
   apply simp
  apply (case_tac "act_state (a # es) = (if (get_entity_activate_bit a = 0)\<or>(get_entity_activate_bit a = 1) then act_state es else False)")
   prefer 2 apply simp
  apply (case_tac "get_entity_activate_bit a = 0 \<or> get_entity_activate_bit a = 1") 
   prefer 2 apply simp
  apply (case_tac "act_cond en a")
   apply simp
  using act_cond.simps
  apply (metis (no_types, opaque_lifting) One_nat_def act_entity entity.exhaust get_entity_name.simps(1) get_entity_name.simps(2) act_name)
  apply simp
  apply (case_tac "en = get_entity_name a") prefer 2 apply simp
  using act_cond.simps
  using act_cond.elims(3) by fastforce 

lemma act_subgoal1:
  assumes "act_state (e#es)"
          "name_uni (e#es)"
  shows   "act_condlist en (e#es) \<Longrightarrow> en \<noteq> get_entity_name (act_entity e) \<Longrightarrow> \<not> act_cond en e \<Longrightarrow>
              get_activate_bit (get_entity en (entity_activation en es)) = 1"
  using assms(2) assms(1) apply simp
  apply (case_tac "get_entity_activate_bit e = 0 \<or> get_entity_activate_bit e = Suc 0") 
   prefer 2 apply simp
  apply simp
  apply (induction es)
   apply simp
  using entity_activated by blast 
                  
definition success_act::"entity_name \<Rightarrow> entity list \<Rightarrow> bool"where"
success_act en es = (get_activate_bit(get_entity en es) = 1)"

theorem act_Ent:
  assumes "act_state (e#es)"
          "name_uni (e#es)"
  shows   "act_condlist en (e#es) \<Longrightarrow> success_act en (entity_activation en (e#es))"
  apply (simp add: success_act_def)
  apply auto prefer 4
  using assms(1) assms(2) name_uni_def apply (simp add: act_subgoal1)
  apply (simp add: act_entity)
  apply (metis act_condlist.simps(2) assms(1) entity_activation.simps(2) get_entity.simps(2) entity_activated)
  apply (metis act_condlist.simps(2) assms(1) entity_activation.simps(2) get_entity.simps(2) entity_activated)
  using act_name by auto
  



lemma act_cond:"act_cond x y \<Longrightarrow> get_activate_bit (hd(entity_activation x (y#ys))) = 1"
  apply auto
  apply (induction y)
  apply (simp add: act_entity)
  using act_entity apply simp
   apply auto
   apply (simp add: change_bit1_def)
  apply (simp add: change_bit1_def)
  using connect apply simp+
  done

theorem act_single_entity :"act_condlist x ys \<Longrightarrow> get_activate_bit(act_entity (cond_entity x ys)) = 1"
  apply simp+
  apply (induction ys)
   apply simp
  apply (simp add: act_cond)
  apply auto
  apply (simp add: act_entity)
  done


(*
lemma judge_nameequal:"judge_nameequal x xs = (fst(fst(snd(x))) = fst(fst(snd(hd(xs)))))"
  apply auto
   apply (induction xs)
    apply simp
   apply (metis (mono_tags, lifting) judge_nameequal.simps(2) list.case_eq_if list.discI)   
  apply (induction xs)
  apply simp
   apply auto
  apply (induction x)
  apply simp
*) 

(*-------------choose task correct--------------*)

lemma choose_cond:"choose_cond x y = (x = fst(y))"
  apply (simp add: choose_cond_def)
  done

lemma choose_correct:"choose_cond y z \<Longrightarrow> fst(choose_task x y (z#zs)) = y"
  apply (induction zs)
   apply auto
  using choose_cond
  apply simp+
  done

theorem choose_Correct:"choose_condlist tn ts \<Longrightarrow> fst(choose_task de tn ts) = tn"
  apply (induction ts) 
   prefer 2
  apply auto
  apply (simp add: choose_cond_def)
  done

(*
  using choose_task_static apply auto[1]
  using choose_task_dynamic 
  apply auto
  done
  sorry*)
(*lemma enter_readyqueue:""*)


(*--------------task activation entity-------------*)

fun target_ent::"entity \<Rightarrow> task \<Rightarrow> task \<Rightarrow> bool"where"
target_ent e t1 t2 = ((get_task_entity_name t1 = get_entity_name e)\<and>(get_task_entity_name t2 = get_entity_name e))"

lemma find_cons:"get_entity_task_name e = fst (get_entity_act e)"
  apply (induction e)
   apply auto
  done

lemma modify_transfer:"get_entity_task_name (modify_entity_task ti e) = (fst(ti))"
  apply (induction e)
   apply auto 
  apply (simp add: connect)
  done

lemma act_equal:"get_entity_task_name (act_entity e) = get_entity_task_name e"
  apply (induction e)
   apply auto
  apply (simp add:connect)
  done

lemma modify_task_bit:"get_entity_task_name (act_entity (modify_entity_task ti e)) = (fst(ti))"
  by (simp add: modify_transfer act_equal)

definition refuse_act::"task \<Rightarrow> entity \<Rightarrow> bool"where"
refuse_act tj e = (act_request tj e = False)"

theorem act_Uni:
  assumes "no_eq_task ti tj"
          "init_act e"
          "target_ent e ti tj"
  shows   "act_request tj (act_task_entity ti e) = False"
  apply auto apply (simp add: act_task_entity_def)
  using assms(2) assms(3)  apply simp
  apply (simp add: act_task_entity_cond_def)
  apply (simp add: find_cons)
  using act_request_def apply simp
  apply (simp add: act_task_entity_cond_def)
  apply (simp add: modify_task_bit)
  using assms(1) no_eq_task_def by auto

(*-----------task execution----------------*)
(*------------condition 1---------------*)
definition get_task_body_beh::"(entity \<times> behavior) \<Rightarrow> behavior"where"
get_task_body_beh x = (snd(x))"
fun inc_beh ::"task_body \<Rightarrow> behavior \<Rightarrow> bool"where"
inc_beh [] beh = False"|"
inc_beh (x#xs) beh = (if fst(get_task_body_beh x) = fst(beh) then True else inc_beh xs beh)" 
definition include_beh::"task \<Rightarrow> behavior \<Rightarrow> bool"where"
include_beh t beh = ((inc_beh (get_task_body t) beh)\<and>((fst(t)) = get_beh_task_name beh))"

fun cont_beh ::"behavior \<Rightarrow> behavior list \<Rightarrow> bool"where"
cont_beh beh [] = False"|"
cont_beh beh (b#bs) = (if fst(beh) = fst(b) then True else cont_beh beh bs)"

theorem excl_Cond1:
  assumes "no_eq_beh beh1 beh2"
          "prop_T t"
          "include_beh t beh1 \<and> include_beh t beh2"  
  shows   "(cont_beh beh1 (get_behlist [t]) \<and> cont_beh beh2 (get_behlist [t])) = False"
  using assms(1) assms(3) apply auto
  apply (case_tac "cont_beh beh1 (get_behlist [t])")
   prefer 2 apply simp
  apply auto
  apply (case_tac "fst beh1 \<noteq> fst (get_beh t)")
   apply simp
  using assms(2) no_eq_beh_def
  apply auto
  done
  


(*-------------condition 2--------------*)
definition exe_req ::"behavior \<Rightarrow> entity \<Rightarrow> bool"where"
exe_req beh e = (if beh_execute_cond beh e then True else False)"
definition is_executing::"behavior \<Rightarrow> entity \<Rightarrow> entity"where"
is_executing beh e = entity_behavior beh (change_visit_bit e)"
definition beh_obj::"behavior \<Rightarrow> entity \<Rightarrow> bool"where"
beh_obj beh e = (get_beh_pas_entity_name beh = get_entity_name e)"

definition beh_re::"behavior \<Rightarrow> entity \<Rightarrow> bool"where"
beh_re beh e = 
((get_visit_bit (change_visit_bit e) = get_visit_bit (entity_behavior beh (change_visit_bit e)))\<and>
(get_entity_name (change_visit_bit e) = get_entity_name (entity_behavior beh (change_visit_bit e))))"


theorem excl_Cond22:
  assumes "prop_T t1 \<and> prop_T t2 \<and> prop_E e"
          "eq_beh beh1 beh2"
          "include_beh t1 beh1 \<and> include_beh t2 beh2"
          "beh_obj beh1 e \<and> beh_obj beh2 e \<and> beh_re beh1 e"
  shows   "get_behlist [t1,t2] = [beh1,beh2] \<Longrightarrow> exe_req beh2 (is_executing beh1 e) = False"
   apply auto
  apply (simp add: exe_req_def) 
  apply (simp add: is_executing_def)
  using assms(1) apply auto
  apply (simp add: prop_E_def)
  using init_vis_def apply auto
  using assms(4) beh_re_def beh_obj_def 
  apply simp
  using beh_execute_cond.simps
  using assms(3) apply simp 
  apply (subgoal_tac "beh_execute_cond beh2 (entity_behavior beh1 (change_visit_bit e)) = False")
   apply simp
  apply (induction e)
  using beh_execute_cond.simps change_visit_bit.simps get_entity_vis.simps get_visit_bit.simps apply auto
   apply (simp add: covert_visit_def) 
   apply (simp add: covert_visit_def) 
  done


definition is_exe::"task \<Rightarrow> entity \<Rightarrow> entity"where"
is_exe t e = (is_executing (hd(get_behlist [t])) e)"

lemma max_len:"length (get_behlist [t]) \<le> 1"
  apply auto
  done

lemma get_all_cond:"get_behlist [t1,t2] = [beh1,beh2] \<Longrightarrow> (get_behlist [t1] = [beh1]\<and>get_behlist [t2] = [beh2])\<or>(get_behlist [t1] = [beh2]\<and>get_behlist [t2] = [beh1])"
  apply auto
   apply (case_tac "get_beh_cond t2 = Fasle")
  apply auto[1]
  apply fastforce
  apply (case_tac "get_beh_cond t1 = Fasle")
  apply simp using max_len
   apply (subgoal_tac "length (get_behlist [t2]) \<noteq> length [beh1,beh2]")
    apply auto[1] apply auto[1]
  apply auto
  by (metis get_behlist.simps(1) list.distinct(1) list.inject)


lemma get_mis_t1: assumes "prop_T t1 \<and> prop_T t2 \<and> prop_E e" 
                  "no_eq_task t1 t2"
                  "include_beh t1 beh1 \<and> include_beh t2 beh2"
                shows"get_behlist [t1] \<noteq> [beh2]"
  apply auto
  apply (simp add: get_beh_cond_def)
  using assms(2) assms(3) no_eq_task_def include_beh_def by auto
 

lemma get_mis: assumes "prop_T t1 \<and> prop_T t2 \<and> prop_E e" 
                  "no_eq_task t1 t2"
                  "include_beh t1 beh1 \<and> include_beh t2 beh2"
                shows"get_behlist [t1,t2] = [beh1,beh2] \<Longrightarrow> (get_behlist [t1] = [beh2]\<and>get_behlist [t2] = [beh1]) =False"
  apply (subgoal_tac "no_eq_task t1 t2 \<Longrightarrow> include_beh t1 beh1 \<and> include_beh t2 beh2 \<Longrightarrow>get_behlist [t1] \<noteq> [beh2]")
   prefer 2 
  using get_mis_t1
  using assms(1) apply blast 
  using assms(2) assms(3) by auto

lemma get_beh_uni: assumes "prop_T t1 \<and> prop_T t2 \<and> prop_E e" 
                  "no_eq_task t1 t2"
                  "include_beh t1 beh1 \<and> include_beh t2 beh2"
          shows   "get_behlist [t1,t2] = [beh1,beh2] \<Longrightarrow> (get_behlist[t1] = [beh1])\<and>(get_behlist[t2] = [beh2])"

  apply (subgoal_tac "get_behlist [t1,t2] = [beh1,beh2] \<Longrightarrow> (get_behlist [t1] = [beh1]\<and>get_behlist [t2] = [beh2])\<or>(get_behlist [t1] = [beh2]\<and>get_behlist [t2] = [beh1])")
   prefer 2 using get_all_cond apply simp
  using get_mis
  using assms(1) assms(2) assms(3) by blast 

lemma task_state_eq:assumes"prop_T t1 \<and> prop_T t2 \<and> prop_E e"
          " no_eq_task t1 t2"
          "include_beh t1 beh1 \<and> include_beh t2 beh2"
          "beh_obj beh1 e \<and> beh_obj beh2 e \<and> beh_re beh1 e"

shows "get_behlist [t1,t2] = [beh1,beh2] \<Longrightarrow> is_exe t1 e = (is_executing beh1 e)"
  apply (subgoal_tac "get_behlist [t1,t2] = [beh1,beh2] \<Longrightarrow> (get_behlist[t1] = [beh1])") prefer 2
  using assms(1) assms(2) assms(3) get_beh_uni apply blast
  apply (simp add: is_exe_def)
  done

definition in_elist::"entity \<Rightarrow> behavior"where"
in_elist e = ('''',op_entity,('''',get_entity_name e,'''',0,0))"


lemma c8:assumes"prop_T t1 \<and> prop_T t2 \<and> prop_E e"
          "no_eq_task t1 t2"
          "include_beh t1 beh1 \<and> include_beh t2 beh2"
          "beh_obj beh1 e \<and> beh_obj beh2 e \<and> beh_re beh1 e"
        shows "get_behlist [t1,t2] = [beh1,beh2] \<Longrightarrow> get_behlist [t2] = [beh2]"
  using get_beh_uni
  using assms(1) assms(2) assms(3) by blast


lemma c9:assumes"prop_T t1 \<and> prop_T t2 \<and> prop_E e"
          "no_eq_task t1 t2"
          "include_beh t1 beh1 \<and> include_beh t2 beh2"
          "beh_obj beh1 e \<and> beh_obj beh2 e \<and> beh_re beh1 e"
        shows "generate_behlist [is_executing beh1 e] = [[in_elist (is_executing beh1 e)]]"
  apply auto using entity_to_behlist_def in_elist_def by auto

lemma c10:assumes"prop_T t1 \<and> prop_T t2 \<and> prop_E e"
          "no_eq_task t1 t2"
          "include_beh t1 beh1 \<and> include_beh t2 beh2"
          "beh_obj beh1 e \<and> beh_obj beh2 e \<and> beh_re beh1 e"
        shows "get_behlist [t1,t2] = [beh1,beh2] \<Longrightarrow> enter_readylist (get_behlist [t2]) (generate_behlist [is_executing beh1 e]) = enter_readylist [beh2] [[in_elist (is_executing beh1 e)]]"
  by (metis assms(1) assms(2) assms(3) assms(4) c8 c9)


lemma c13:assumes"prop_T t1 \<and> prop_T t2 \<and> prop_E e"
          "no_eq_task t1 t2"
          "include_beh t1 beh1 \<and> include_beh t2 beh2"
          "beh_obj beh1 e \<and> beh_obj beh2 e \<and> beh_re beh1 e"
        shows "get_behlist [t1,t2] = [beh1,beh2] \<Longrightarrow> enter_blist beh2 [[in_elist (is_executing beh1 e)]] = [[beh2,in_elist (is_executing beh1 e)]]"
  apply auto using beh_entity_name_equal_def in_elist_def apply simp
  using assms(4) beh_obj_def apply auto
  apply (simp add:get_beh_pas_entity_name_def)
  apply (subgoal_tac "get_entity_name e = get_entity_name (change_visit_bit e)") prefer 2
   apply (induction e)
  apply auto[1] apply auto[2]
  apply (simp add: beh_re_def is_executing_def)
  done
  

lemma c11:assumes"prop_T t1 \<and> prop_T t2 \<and> prop_E e"
          " no_eq_task t1 t2"
          "include_beh t1 beh1 \<and> include_beh t2 beh2"
          "beh_obj beh1 e \<and> beh_obj beh2 e \<and> beh_re beh1 e"
        shows "get_behlist [t1,t2] = [beh1,beh2] \<Longrightarrow> enter_readylist [beh2] [[in_elist (is_executing beh1 e)]] = [[beh2,in_elist (is_executing beh1 e)]]"
  by (metis assms(1) assms(2) assms(3) assms(4) c13 enter_readylist.simps(3) enter_readylist.simps(4))


lemma c12:assumes"prop_T t1 \<and> prop_T t2 \<and> prop_E e"
          "no_eq_task t1 t2"
          "include_beh t1 beh1 \<and> include_beh t2 beh2"
          "beh_obj beh1 e \<and> beh_obj beh2 e \<and> beh_re beh1 e"
        shows "get_behlist [t1,t2] = [beh1,beh2] \<Longrightarrow> enter_readylist (get_behlist [t2]) (generate_behlist [is_executing beh1 e]) = [[beh2,in_elist (is_executing beh1 e)]]"
  by (metis (full_types) assms(1) assms(2) assms(3) assms(4) c10 c11)

lemma c14:assumes"prop_T t1 \<and> prop_T t2 \<and> prop_E e"
          " no_eq_task t1 t2"
          "include_beh t1 beh1 \<and> include_beh t2 beh2"
          "beh_obj beh1 e \<and> beh_obj beh2 e \<and> beh_re beh1 e"
        shows "get_behlist [t1,t2] = [beh1,beh2] \<Longrightarrow> execute_corbeh (enter_readylist (get_behlist [t2]) (generate_behlist [is_executing beh1 e])) [is_executing beh1 e] = execute_corbeh [[beh2,in_elist (is_executing beh1 e)]] [is_executing beh1 e]"
  by (metis assms(1) assms(2) assms(3) assms(4) c12)

lemma c16:assumes"prop_T t1 \<and> prop_T t2 \<and> prop_E e"
          "no_eq_task t1 t2"
          "include_beh t1 beh1 \<and> include_beh t2 beh2"
          "beh_obj beh1 e \<and> beh_obj beh2 e \<and> beh_re beh1 e"
        shows " execute_corbeh [[beh2,in_elist (is_executing beh1 e)]] [is_executing beh1 e] = execute_behaviors [beh2,in_elist (is_executing beh1 e)] [is_executing beh1 e]"
  by (metis (no_types, opaque_lifting) execute_corbeh.simps(1) execute_corbeh.simps(3) execute_corbeh.simps(4) list.exhaust)



lemma v1:assumes"prop_T t1 \<and> prop_T t2 \<and> prop_E e"
          "no_eq_task t1 t2"
          "include_beh t1 beh1 \<and> include_beh t2 beh2"
          "beh_obj beh1 e \<and> beh_obj beh2 e \<and> beh_re beh1 e"
        shows "get_behlist [t1,t2] = [beh1,beh2] \<Longrightarrow> multitasks_con [t2] [is_exe t1 e] = execute_corbeh [[beh2,in_elist (is_exe t1 e)]] [is_exe t1 e]"
  by (smt (verit, ccfv_SIG) assms(1) assms(2) assms(3) assms(4) c12 task_state_eq multitasks_con.simps(2))



lemma v2: assumes "prop_T t1 \<and> prop_T t2 \<and> prop_E e"
          "no_eq_task t1 t2"
          "include_beh t1 beh1 \<and> include_beh t2 beh2"
          "beh_obj beh1 e \<and> beh_obj beh2 e \<and> beh_re beh1 e"
        shows   "get_behlist [t1,t2] = [beh1,beh2] \<Longrightarrow> multitasks_con [t2] [is_exe t1 e] = multitasks_con [t2] [is_executing beh1 e]"
  by (metis assms(1) assms(2) assms(3) assms(4) task_state_eq)

lemma v3: assumes "prop_T t1 \<and> prop_T t2 \<and> prop_E e"
          "no_eq_task t1 t2"
          "include_beh t1 beh1 \<and> include_beh t2 beh2"
          "beh_obj beh1 e \<and> beh_obj beh2 e \<and> beh_re beh1 e"
        shows   "get_behlist [t1,t2] = [beh1,beh2] \<Longrightarrow> multitasks_con [t2] [is_executing beh1 e] = execute_corbeh [[beh2,in_elist (is_executing beh1 e)]] [is_executing beh1 e]"
  by (metis assms(1) assms(2) assms(3) assms(4) get_beh_uni is_exe_def list.sel(1) v1)

lemma beh_excl_init:
  assumes "prop_T t1 \<and> prop_T t2 \<and> prop_E e"
          "no_eq_task t1 t2"
          "include_beh t1 beh1 \<and> include_beh t2 beh2"
          "beh_obj beh1 e \<and> beh_obj beh2 e \<and> beh_re beh1 e"
        shows   "execute_behavior (in_elist (is_executing beh1 e)) [is_executing beh1 e] = [is_executing beh1 e]"

  apply (subgoal_tac "beh_execute_cond (in_elist (is_executing beh1 e)) (is_executing beh1 e) = False")
   apply auto
  apply (subgoal_tac "beh_execute_cond (in_elist (is_executing beh1 e)) (is_executing beh1 e) = False")
   apply auto
  apply (subgoal_tac "fst (in_elist (is_executing beh1 e)) = ''''") prefer 2
  apply (simp add: in_elist_def)
  apply (induction e)
  using beh_execute_cond.simps in_elist_def
  apply (meson beh_execute_cond.elims(2))
  using beh_execute_cond.elims(1) by blast 


lemma beh_excl_com: 
  assumes "prop_T t1 \<and> prop_T t2 \<and> prop_E e"
          "no_eq_task t1 t2"
          "include_beh t1 beh1 \<and> include_beh t2 beh2"
          "beh_obj beh1 e \<and> beh_obj beh2 e \<and> beh_re beh1 e"
        shows   "execute_behavior beh2 [is_executing beh1 e] = [is_executing beh1 e]"
  apply (subgoal_tac "beh_execute_condlist beh2 [is_executing beh1 e] = False")
   apply auto
  apply (subgoal_tac "beh_execute_cond beh2 (is_executing beh1 e) = False") 
   apply auto
  using assms(1) 
  apply (simp add: prop_E_def init_vis_def)
  apply (simp add: is_executing_def)
using assms(4) apply (simp add: beh_re_def)
  apply (induction e)
  apply auto apply (simp add: covert_visit_def)
  apply (case_tac "covert_visit 0 = 0") 
  using covert_visit_def apply simp
  apply auto
  done


lemma beh_exe_excl:
  assumes "prop_T t1 \<and> prop_T t2 \<and> prop_E e"
          "no_eq_task t1 t2"
          "include_beh t1 beh1 \<and> include_beh t2 beh2"
          "beh_obj beh1 e \<and> beh_obj beh2 e \<and> beh_re beh1 e"
        shows   "execute_behaviors [beh2,in_elist (is_executing beh1 e)] [is_executing beh1 e] = [is_executing beh1 e]"
  by (metis assms(1) assms(2) assms(3) assms(4) execute_behaviors.simps(3) execute_behaviors.simps(4) beh_excl_com beh_excl_init)
  
  
lemma task_exe_excl:
  assumes "prop_T t1 \<and> prop_T t2 \<and> prop_E e"
          "no_eq_task t1 t2"
          "include_beh t1 beh1 \<and> include_beh t2 beh2"
          "beh_obj beh1 e \<and> beh_obj beh2 e \<and> beh_re beh1 e"
        shows   "get_behlist [t1,t2] = [beh1,beh2] \<Longrightarrow> multitasks_con [t2] [is_executing beh1 e] = [is_executing beh1 e]"
  by (metis assms(1) assms(2) assms(3) assms(4) c16 v3 beh_exe_excl)
  
theorem excl_Cond2:
  assumes "prop_T t1 \<and> prop_T t2 \<and> prop_E e"
          "eq_beh beh1 beh2 \<and> no_eq_task t1 t2"
          "include_beh t1 beh1 \<and> include_beh t2 beh2"
          "beh_obj beh1 e \<and> beh_obj beh2 e \<and> beh_re beh1 e"
  shows   "get_behlist [t1,t2] = [beh1,beh2] \<Longrightarrow> multitasks_con [t2] [is_exe t1 e] = [is_exe t1 e]"
  using assms(1) assms(2) assms(3) assms(4) 
  apply (subgoal_tac "is_exe t1 e = (is_executing beh1 e)") prefer 2
  using task_state_eq apply blast 
  apply (subgoal_tac  "get_behlist [t1,t2] = [beh1,beh2] \<Longrightarrow> 
          (get_behlist[t1] = [beh1])\<and>(get_behlist[t2] = [beh2])") defer
  apply (metis get_beh_uni)
  apply (subgoal_tac "execute_behaviors [beh2,in_elist (is_executing beh1 e)] [is_executing beh1 e]
           = [is_executing beh1 e]") defer
   apply (metis assms(1) execute_behaviors.simps(4) beh_exe_excl)
  by (metis task_exe_excl)


(*-------------condition 3--------------*)

theorem excl_Cond3:
  assumes "prop_T t1 \<and> prop_T t2 \<and> prop_E e"
          "no_eq_beh beh1 beh2 \<and> no_eq_task t1 t2"
          "include_beh t1 beh1 \<and> include_beh t2 beh2"
          "beh_obj beh1 e \<and> beh_obj beh2 e \<and> beh_re beh1 e"
  shows   "get_behlist [t1,t2] = [beh1,beh2] \<Longrightarrow> multitasks_con [t2] [is_exe t1 e] = [is_exe t1 e]"
  using assms(1) assms(2) assms(3) assms(4) 
  apply (subgoal_tac "is_exe t1 e = (is_executing beh1 e)") prefer 2
  using task_state_eq apply blast 
  apply (subgoal_tac  "get_behlist [t1,t2] = [beh1,beh2] \<Longrightarrow> 
          (get_behlist[t1] = [beh1])\<and>(get_behlist[t2] = [beh2])") defer
   apply (metis get_beh_uni)
  apply (subgoal_tac "execute_behaviors [beh2,in_elist (is_executing beh1 e)] [is_executing beh1 e] = [is_executing beh1 e]") defer
   apply (metis assms(1) execute_behaviors.simps(4) beh_exe_excl)
  by (metis task_exe_excl)

theorem excl_Cond33:
  assumes "prop_T t1 \<and> prop_T t2 \<and> prop_E e"
          "no_eq_beh beh1 beh2"
          "include_beh t1 beh1 \<and> include_beh t2 beh2"
          "beh_obj beh1 e \<and> beh_obj beh2 e \<and> beh_re beh1 e" 
  shows   "get_behlist [t1,t2] = [beh1,beh2] \<Longrightarrow> exe_req beh2 (is_executing beh1 e) = False"
   apply auto
  apply (simp add: exe_req_def) 
  apply (simp add: is_executing_def)
  using assms(1) apply auto
  apply (simp add: prop_E_def)
  using init_vis_def apply auto
  using assms(4) beh_re_def beh_obj_def 
  apply simp
  using beh_execute_cond.simps
  using assms(3) apply simp 
  apply (subgoal_tac "beh_execute_cond beh2 (entity_behavior beh1 (change_visit_bit e)) = False")
   apply simp
  apply (induction e)
  using beh_execute_cond.simps change_visit_bit.simps get_entity_vis.simps get_visit_bit.simps apply auto
   apply (simp add: covert_visit_def) 
   apply (simp add: covert_visit_def) 
  done
 

 

(* execute_corbeh [[beh2]] [e] = e  *)

lemma act:"is_activating y \<Longrightarrow> act_cond x y = False"
  apply auto
  apply (simp add: is_activating_def)
  apply (induction y)
   apply simp
  apply auto
  done

theorem act_exclusion:"is_activating y \<Longrightarrow> entity_activation x (y#ys) = y#(entity_activation x ys)"
  apply auto
   apply (simp add: is_activating_def)
   apply (induction y)
    apply simp+
  apply (induction y)
   apply (simp add: is_activating_def)
  apply auto
  using is_activating_def by simp

(*------------------------*)
(*------------------------*)
(*------------------------*)
end