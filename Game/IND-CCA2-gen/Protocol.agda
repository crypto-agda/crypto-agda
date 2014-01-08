
open import Type
open import Control.Protocol.Core
open import Function

module Game.IND-CCA2-gen.Protocol
  -- could be Public Key
  (Public    : ★)
  -- could be Ciphertext
  (Query : ★)
  -- could be Message
  (Response : Query → ★)
  -- could be Ciphertext or pair of Ciphertext in CCA2-dagger
  (Challenge : ★)
  -- could be a pair of Messages or unit if no input required
  (ChallengeInput : ★)
  where


CCARound : Proto → Proto
CCARound = Server' Query Response

CCAChal : Proto → Proto
CCAChal X = ChallengeInput →' (Challenge ×' X)

-- challenger implement this
CCA2-gen : Proto
CCA2-gen = Public ×' CCARound (CCAChal (CCARound end))
