// Project: Project 1
// Team: Team 5
// Model for system: Nicebook

/** File Description **/
// privacy.als: containing the enum and signature for privacy level

open nicebook

/** Run Commands **/
// General case.
run generalNicebook {
    all n : Nicebook | invariant[n]
}

// Check multiple friendships.
run threeUserNicebook {
    all n : Nicebook | invariant[n]
} for 5 but exactly 3 User

// Check multiple comments.
run commentsNicebook {
    all n : Nicebook | invariant[n]
} for 5 but exactly 3 Comment

// Check multiple tags.
run commentsNicebook {
    all n : Nicebook | invariant[n] and #n.tags > 3
} for 5

// Check multiple publishables with one having more than one tags.
run publishablesNicebook {
    all n : Nicebook | invariant[n] and #n.tags > 3
} for 5 but exactly 3 Publishable

// Check multiple publishables with one having more than one tags.
run publishablesNicebook {
    all n : Nicebook | invariant[n]
    some note : Note | #note.photo > 2
} for 5 but exactly 3 Photo



