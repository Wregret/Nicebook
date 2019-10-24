// Project: Project 1
// Team: Team 5
// Model for system: Nicebook

open privacy

/** Signatures **/
one sig Nicebook {
    posts : User -> some Content,   // Contents created by users
    friends : User -> set User      // Friendships between users
}
sig User {
    wall : one Wall
}
sig Wall {
    notes : set Note,
    photos : set Photo
}
sig Tag {
    noteTag : Note -> one User,
    photoTag : Photo -> one User
}

abstract sig Content {
    privacyLevel : PrivacyLevel
}
sig Note extends Content {
    photo : set Photo,
    noteComment : set Comment
}
sig Photo extends Content {
    photoComment : set Comment
}
sig Comment extends Content {
    commentComment: set Comment
}

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
/** Signature Invariant **/
pred nicebookInvariant[n : Nicebook] {
    noSelfFriendship[n]
    sysmetricFriendship[n]
}

pred commentInvariant[c : Comment] {
    noSelfComment[c]
    noOrphanComment[c]
}

pred tagInvariant[t : Tag, n : Nicebook] {
    // only the owner of a note can tag his / her friends
    all u1, u2 : User, note : Note |
        note in n.posts[u1] and u2 in t.noteTag[note] implies
        u2 in n.friends[u1]
    // only the owner of a photo can tag his / her friends
    all u1, u2 : User, photo : Photo |
        photo in n.posts[u1] and u2 in t.photoTag[photo] implies
        u2 in n.friends[u1]
}

pred contentInvariant[n : Nicebook] {
    // a content must be owned by one user
    all c : Content |
        #n.posts.c = 1
}

pred wallInvariant[n : Nicebook] {
    // all the notes and photos posted on the user's wall must be 
    // owned by the user or his / her friends
    all u1, u2 : User |
        u1.wall.notes in n.posts[u2]
        implies (u2 in n.friends[u1] or u1 = u2)
    // every user has his / her unique wall
    all u1, u2 : User |
        u1 != u2 implies u1.wall != u2.wall
    // a wall must be owned by a user
    all w : Wall |
        #wall.w = 1
}

/** Helper Invariant **/
pred noSelfFriendship[n : Nicebook] {
    // no user be a friend with himself
    no iden & n.friends
}

pred sysmetricFriendship[n : Nicebook] {
    // sysmetric friendship
    all u1, u2 : User |
        u1 in n.friends[u2] implies u2 in n.friends[u1]
}

pred noSelfComment[c : Comment] {
    // no comment can comment itself
    // no circular comments
    c not in c.^commentComment
}

pred noOrphanComment[c : Comment] {
    // a comment must be associated to a note or a photo or another comment
    some n : Note |
        c in n.noteComment
    or
    some p : Photo |
        c in p.photoComment
    or
    some comment : Comment |
        c in comment.commentComment and c != comment
}

// run command
run generateNicebook {
    all n : Nicebook |
        nicebookInvariant[n] and
        wallInvariant[n] and
        contentInvariant[n]
    all n : Nicebook, t : Tag |
        tagInvariant[t, n]
    all c : Comment |
        commentInvariant[c]
}