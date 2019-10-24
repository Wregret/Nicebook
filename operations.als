// Project: Project 1
// Team: Team 5
// Model for system: Nicebook

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
