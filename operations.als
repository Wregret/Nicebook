// Project: Project 1
// Team: Team 5
// Model for system: Nicebook

// NOTE: use privacy level (int) to enforce privacy settings

open nicebook
/** Operations **/
pred upload[n, n' : Nicebook, u : User, c : Content] {
    n'.friends = n.friends
    n'.posts = n.posts + u -> c
}

pred remove[n, n' : Nicebook, u : User, c : Content] {
    n'.friends = n.friends
    n'.posts = n.posts - u -> c
}

run {
    some n : Nicebook |
        nicebookInvariant[n]
}