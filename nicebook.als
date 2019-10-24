// Project: Project 1
// Team: Team 5
// Model for system: Nicebook

// NOTE: relational approach for privacy implementation
//       - viewable : User

open privacy

/** Signatures **/
one sig Nicebook {
    posts : User -> Content,   // Contents created by users
    friends : User -> User      // Friendships between users
}
sig User {
    wall : one Wall
}
sig Wall {
    notes : set Note,
    photos : set Photo
}

abstract sig Tag {}
sig NoteTag extends Tag {}
sig PhotoTag extends Tag {}

abstract sig Content {
    privacyLevel : PrivacyLevel
}
sig Note extends Content {
    photo : set Photo,
    noteComment : set Comment
}
sig Photo extends Content {
    photoCommnet : set Comment
}
sig Comment extends Content {}

/** Functions **/
fun getOnlyMe[u : User] : set User{
    u
}

fun getFriends[n : Nicebook, u : User] : set User {
    n.friends[u]
}

fun getFriendsOfFriends[n : Nicebook, u : User] : set User {
    n.friends[n.friends[u]]
}

fun getEveryone[n : Nicebook] : set User {
    n.friends.User
}

/** Invairants **/
pred nicebookInvariant[n : Nicebook] {
    // no user be a friend with himself
    all u : n.friends.User |
        u not in n.friends[u] and
        u not in n.friends.u
    // sysmetric friendship
    all u1, u2 : User |
        u1 in n.friends[u2] implies u2 in n.friends[u1]
}

run {
    some n : Nicebook |
        nicebookInvariant[n]
}