// Project: Project 1
// Team: Team 5
// Model for system: Nicebook

open privacy

/** Signatures **/
one sig Nicebook {
    posts : User -> some Content,   // Contents created by users
    friends : User -> set User,     // Friendships between users
    tag : Publishable -> one User   // Tags from publishable contents to users
}
sig User {
    wall : one Wall
}
sig Wall {
    publishables : set Publishable
}

abstract sig Content {
    privacyLevel : PrivacyLevel
}
abstract sig Publishable extends Content {
    publishableComment : set Comment
}
sig Note extends Publishable {
    photo : set Photo,
}
sig Photo extends Publishable {}
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

pred tagInvariant[n : Nicebook] {
    // only the owner of a publishable content can tag his / her friends
    all u1, u2 : User, p : Publishable |
        p in n.posts[u1] and u2 in n.tag[p] implies
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
    some p : Publishable |
        c in p.publishableComment
    or
    some comment : Comment |
        c in comment.commentComment and c != comment
}

// run command
run generateNicebook {
    all n : Nicebook |
        nicebookInvariant[n] and
        contentInvariant[n] and
        wallInvariant[n] and
        tagInvariant[n]
    all c : Comment |
        commentInvariant[c]
}