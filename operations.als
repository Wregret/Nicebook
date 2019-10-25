// Project: Project 1
// Team: Team 5
// Model for system: Nicebook

open nicebook

/** Operations **/
pred upload[n, n' : Nicebook, u : User, c : Content] {
    // pre condition
    u -> c not in n.posts

    // frame condition
    n'.tags = n.tags
    n'.friends = n.friends

    // post condition
    n'.posts = n.posts + u -> c
}

pred remove[n, n' : Nicebook, u : User, c : Content] {
    // pre condition
    u -> c in n.posts

    // frame condition
    n'.tags = n.tags
    n'.friends = n.friends

    // post condition
    n'.posts = n.posts - u -> c
}

// pred publish[n, n' : Nicebook, p : Publishable] {
//     n'.friends = n.friends


//     let u = n.posts.p |
//         let w = u.wall |
//             // precondition
//             // the publishable contents should not be on the wall already
//             p not in w.publishables

// }

/** Assertion **/