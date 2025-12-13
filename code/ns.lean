-- Public keys are universally known
-- A to B:  {Na, A}_Pub(B)
-- B to A:  {Na, Nb}_Pub(A)
-- A to B:  {Nb}_Pub(B)

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Finset.Card

inductive AgentId where | Alice | Bob | Charlie
 deriving Repr, BEq, DecidableEq

inductive Nonce where | Na | Nb | Nc
 deriving Repr, BEq, DecidableEq

structure PublicKey where
  id : AgentId
deriving Repr, BEq, DecidableEq

structure PrivateKey where
  id : AgentId
deriving Repr, BEq, DecidableEq

def pub_of_priv (privK : PrivateKey) : PublicKey:=
  {id := privK.id}

--def priv_of_pub (pubK : PublicKey) : PrivateKey :=
 -- {id := pubK.id}

def mkPubKey (id : AgentId) : PublicKey :=
  {id := id}

def mkPrivKey (id : AgentId) : PrivateKey :=
  {id := id}

inductive Message where
  | agent ( id : AgentId)
  | nonce ( n  : Nonce)
  | pair (m1 m2 : Message)
  | enc (msg : Message) (key : PublicKey)
  | privkey (key : PrivateKey)
  | pubkey (key : PublicKey)
deriving Repr, BEq, DecidableEq
-- Read about DecidableEq

def Encryption (msg : Message) (key : PublicKey)
  : Message :=
  .enc msg key

def Decryption (encMsg : Message) (privK : PrivateKey)
  : Option Message:=
  match encMsg with
  | .enc msg key =>
    if key == pub_of_priv privK then some msg
    else none
  | _ => none

inductive AgentState where
  | idle
  | alice_waiting_for_2 (partner : AgentId) (na : Nonce)
  | bob_waiting_for_3   (partner : AgentId) (na : Nonce) (nb : Nonce)
  | done (partner : AgentId) (sent_nonce  received_nonce : Nonce)
deriving Repr, BEq, DecidableEq

abbrev KnowledgeSet := Finset Message

structure WorldState where
  alice_state : AgentState
  bob_state  : AgentState
  attacker_knowledge : KnowledgeSet
deriving BEq

inductive CanDeduce : KnowledgeSet → Message → Prop where
  | dy_axiom :
    ∀ (knowledge : KnowledgeSet) (msg : Message), msg ∈ knowledge →
    CanDeduce knowledge msg
  | compose :
    ∀ (knowledge : KnowledgeSet) (msg1 msg2 : Message),
    CanDeduce knowledge msg1 →
    CanDeduce knowledge msg2 →
    CanDeduce knowledge (.pair msg1 msg2)
  | decompose_fst :
    ∀ (knowledge : KnowledgeSet) (msg1 msg2 : Message),
    CanDeduce knowledge (.pair msg1 msg2) →
    CanDeduce knowledge msg1
  | decompose_snd :
    ∀ (knowledge : KnowledgeSet) (msg1 msg2 : Message),
    CanDeduce knowledge (.pair msg1 msg2) →
    CanDeduce knowledge msg2
  | decryption :
    ∀ (knowledge : KnowledgeSet) (privk : PrivateKey) (msg : Message),
    CanDeduce knowledge (.enc msg (pub_of_priv privk)) →
    CanDeduce knowledge (.privkey privk) →
    CanDeduce knowledge msg
  | encryption :
    ∀ (knowledge : KnowledgeSet) (pubk : PublicKey) (msg : Message),
    CanDeduce knowledge msg →
    CanDeduce knowledge (.pubkey pubk) →
    CanDeduce knowledge (.enc msg pubk)


inductive Step
  : WorldState → WorldState → Prop where
  | alice_initiates :
    ∀ (state : WorldState) (partner : AgentId) (na : Nonce) (msg : Message),
    state.alice_state = .idle →
    msg = .enc (.pair (.nonce na) (.agent .Alice)) (mkPubKey partner) →
    Step state {
            state with
                alice_state := (.alice_waiting_for_2 partner na)
                attacker_knowledge := ({msg} ∪ state.attacker_knowledge)
    }
  | bob_responds :
    ∀ (state : WorldState) (partner : AgentId) (na nb : Nonce)
      (msg : Message),
      state.bob_state = .idle →
      msg = .enc (.pair (.nonce na) (.agent partner)) (mkPubKey .Bob) →
      CanDeduce state.attacker_knowledge msg →
      Step state {
              state with
                bob_state := (.bob_waiting_for_3 partner na nb)
                attacker_knowledge := {
                  .enc (.pair (.nonce na) (.nonce nb)) (mkPubKey partner)
                } ∪ state.attacker_knowledge
      }
  | alice_completes :
    ∀ (state : WorldState) (partner : AgentId) (na nb : Nonce)
      (msg : Message),
      state.alice_state = .alice_waiting_for_2 partner na →
      msg = (.enc (.pair (.nonce na) (.nonce nb)) (mkPubKey .Alice)) →
      CanDeduce state.attacker_knowledge msg →
      Step state {
                  state with
                  alice_state := .done partner na nb
                  attacker_knowledge := {
                    .enc (.nonce nb) (mkPubKey partner)
                  } ∪ state.attacker_knowledge
      }
  | bob_completes :
    ∀ (state : WorldState) (partner : AgentId) (na nb : Nonce)
      (msg : Message),
      state.bob_state = .bob_waiting_for_3 partner na nb →
      msg = (.enc (.nonce nb) (mkPubKey .Bob)) →
      CanDeduce state.attacker_knowledge msg →
      Step state {
                  state with
                  bob_state := .done partner nb na
      }

abbrev Reachable
 : WorldState → WorldState → Prop :=
  Relation.ReflTransGen Step

-- How Lowe's attack works
-- Honest run
--- A to B:  {Na, A}_Pub(B)
-- B to A:  {Na, Nb}_Pub(A)
-- A to B:  {Nb}_Pub(B)

-- A to C: {Na, A}_Pub(C)
-- C to B: {Na, A}_Pub(B)
-- B to A: {Na, Nb}_Pub(A)
-- A to C: {Nb}_Pub(C) // Nb leaked to C
-- C to B: {Nb}_Pub(A)
-- B thinks it's taking to A and sends data which will be decrypted as Nb is known
def s_init : WorldState :=
  {
    alice_state := .idle
    bob_state   := .idle
    attacker_knowledge :=
        [.agent .Alice, .agent .Bob, .agent .Charlie,
          .nonce .Nc, .pubkey (mkPubKey .Alice),
          .pubkey (mkPubKey .Bob),
          .pubkey (mkPubKey .Charlie), .privkey {id:=.Charlie}].toFinset
  }

lemma CanDeduce_mono {K K' : KnowledgeSet} {m : Message} (h_sub : K ⊆ K')
  : CanDeduce K m → CanDeduce K' m
  := by
  intro h_deduce
  induction h_deduce
  case dy_axiom msg h_mem =>
    apply CanDeduce.dy_axiom
    exact h_sub h_mem
  case compose msg1 msg2 kmsg1 kmsg2 k'msg1 k'msg2 =>
    apply CanDeduce.compose
    · exact k'msg1
    · exact k'msg2
  case decompose_fst msg1 msg2 knw ih =>
    apply CanDeduce.decompose_fst (K') (msg1) (msg2)
    exact ih
  case decompose_snd msg1 msg2 knw ih =>
    apply CanDeduce.decompose_snd (K') (msg1)
    exact ih
  case decryption privK msg enc key ih_enc ih_key =>
    apply CanDeduce.decryption K' privK
    · exact ih_enc
    · exact ih_key
  case encryption pubK msg c_msg enc_msg ih_c_msg ih_enc_msg =>
    apply CanDeduce.encryption
    · exact ih_c_msg
    · exact ih_enc_msg

macro "mono_r" : tactic => `(tactic| repeat(apply CanDeduce_mono Finset.subset_union_right))

theorem lowes_attack (na nb : Nonce) :
  ∃ (s_final : WorldState), Reachable s_init s_final ∧
  s_final.alice_state = .done .Charlie na nb ∧
  s_final.bob_state = .done .Alice nb na ∧
  CanDeduce s_final.attacker_knowledge (.nonce nb)
  := by
  let s1 : WorldState := {
    s_init with
    alice_state := (.alice_waiting_for_2 .Charlie na)
    attacker_knowledge := {.enc (.pair (.nonce na) (.agent .Alice)) (mkPubKey .Charlie)}
     ∪ s_init.attacker_knowledge
  }
  have h1 : Step s_init s1 := by
    apply Step.alice_initiates
    · rfl
    · rfl
  let s2 : WorldState := {
    s1 with
    bob_state := .bob_waiting_for_3 .Alice na nb
    attacker_knowledge := {.enc (.pair (.nonce na) (.nonce nb)) (mkPubKey .Alice)}
     ∪  s1.attacker_knowledge
  }
  let s3 : WorldState := {
    s2 with
    alice_state := .done .Charlie na nb
    attacker_knowledge := {.enc (.nonce nb)  (mkPubKey .Charlie)}
     ∪ s2.attacker_knowledge
  }
  let s4 : WorldState := {
    s3 with
    bob_state := .done .Alice nb na
  }
  have h2 : Step s1 s2 := by
    apply Step.bob_responds
    · rfl
    · rfl
    have h_can_deduce_msg_for_bob :
    CanDeduce s1.attacker_knowledge (.enc (.pair (.nonce na) (.agent .Alice)) (mkPubKey .Bob)) := by
      have h_knows_encrypted
      : CanDeduce
        s1.attacker_knowledge (.enc (.pair (.nonce na) (.agent .Alice)) (mkPubKey .Charlie))
      := by
        apply CanDeduce.dy_axiom
        simp only [s1]
        apply Finset.mem_union_left
        apply Finset.mem_singleton_self
      have h_knows_charlie_privK : CanDeduce s1.attacker_knowledge (.privkey {id := .Charlie}) := by
        mono_r
        apply CanDeduce.dy_axiom; simp [s_init]
      have h_deduce_pair : CanDeduce s1.attacker_knowledge (.pair (.nonce na) (.agent .Alice)) := by
        apply CanDeduce.decryption _ ({id := .Charlie})
        exact h_knows_encrypted
        exact h_knows_charlie_privK
      have h_knows_bob_pubK : CanDeduce s1.attacker_knowledge (.pubkey (mkPubKey .Bob)) := by
        mono_r
        apply CanDeduce.dy_axiom; simp [s_init]
      apply CanDeduce.encryption
      · exact h_deduce_pair
      · exact h_knows_bob_pubK
    · exact h_can_deduce_msg_for_bob
  have h3 : Step s2 s3 := by
    apply Step.alice_completes
    · rfl
    · rfl
    · apply CanDeduce.dy_axiom
      unfold s2
      apply Finset.mem_union_left
      apply Finset.mem_singleton_self
  have h_charlie_knows_bobs_nonce :
    CanDeduce s3.attacker_knowledge (Message.nonce nb) := by
    have h_knows_encrypted :
      CanDeduce s3.attacker_knowledge ((Message.nonce nb).enc (mkPubKey AgentId.Charlie)) := by
        apply CanDeduce.dy_axiom
        unfold s3
        apply Finset.mem_union_left
        apply Finset.mem_singleton_self
    have h_knows_charlie_privK : CanDeduce s3.attacker_knowledge (.privkey {id := .Charlie}) := by
      mono_r
      apply CanDeduce.dy_axiom; simp [s_init]
    apply CanDeduce.decryption _ {id := .Charlie}
    exact h_knows_encrypted
    exact h_knows_charlie_privK
  have h4 : Step s3 s4 := by
    apply Step.bob_completes
    · rfl
    · rfl
    have h_can_deduce_msg_for_bob :
    CanDeduce s3.attacker_knowledge ((Message.nonce nb).enc (mkPubKey AgentId.Bob)) := by
      have h_knows_charlie_privK : CanDeduce s3.attacker_knowledge (.privkey {id := .Charlie}) := by
        mono_r
        apply CanDeduce.dy_axiom; simp [s_init]
      have h_knows_bob_pubK :
      CanDeduce s3.attacker_knowledge (Message.pubkey (mkPubKey .Bob)) := by
        mono_r
        apply CanDeduce.dy_axiom; simp [s_init]
      apply CanDeduce.encryption
      exact h_charlie_knows_bobs_nonce
      exact h_knows_bob_pubK
    exact h_can_deduce_msg_for_bob
  use s4
  constructor
  · apply Relation.ReflTransGen.head
    · exact h1
    apply Relation.ReflTransGen.head
    · exact h2
    apply Relation.ReflTransGen.head
    · exact h3
    apply Relation.ReflTransGen.head
    · exact h4
    apply Relation.ReflTransGen.refl
  constructor
  · rfl
  constructor
  · rfl
  exact h_charlie_knows_bobs_nonce
