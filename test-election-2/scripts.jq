 jq '.answers[0] | {c: .choices[0], i: .individual_proofs[0]}' test-election-2/np-vote.json
