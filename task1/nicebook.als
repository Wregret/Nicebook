// Project: Project 1
// Team: Team 5
// Model for system: Nicebook

open privacy

/** Signatures **/
one sig Nicebook {
    posts : User -> some Content,   // Contents created by users
    friends : User -> set User,     // Friendships between users
    tags : Publishable -> some User // Tags from publishable contents to users
}
sig User {}
sig Wall {
    owner : one User,
    wallPrivacy : one PrivacyLevel
}

abstract sig Content {
    contentPrivacy : one PrivacyLevel,
    comments : set Comment
}
abstract sig Publishable extends Content {
    wall : set Wall
}
sig Note extends Publishable {
    photo : set Photo,
}
sig Photo extends Publishable {}
sig Comment extends Content {}

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
    // 1. only friends can be tagged
    all u1, u2 : User, p : Publishable |
        (p in n.posts[u1] and u2 in n.tags[p]) implies
        u2 in n.friends[u1]

    // 2. if some user is tagged in a publishable content, 
    //    then the content must be on his / her wall
    // 3. a publishable content can only have tags if it has been published
    all u : User, p : Publishable |
        (u in n.tags[p] or u = n.posts.p) iff u in p.wall.owner
}

pred contentInvariant[n : Nicebook] {
    // a content must be owned by one user
    all c : Content |
        #n.posts.c = 1
}

pred wallInvariant[n : Nicebook] {
    // every user has his / her unique wall
    all w1, w2 : Wall |
        w1 != w2 implies w1.owner != w2.owner
    // a user must own a wall
    all u : User |
        #owner.u = 1
    // all publishable contents on any wall must have been uploaded
    all p : Publishable |
        #p.wall > 0 implies #n.posts.p = 1
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
    c not in c.^comments
}

pred noOrphanComment[c : Comment] {
    // a comment must be associated to a note or a photo or another comment
    some p : Publishable |
        c in p.comments
    or
    some comment : Comment |
        c in comment.comments and c != comment
}

// Total invariant
pred invariant[n : Nicebook] {
        nicebookInvariant[n] and
        contentInvariant[n] and
        wallInvariant[n] and
        tagInvariant[n] and
    all c : Comment |
        commentInvariant[c]
}

// run command
run generateNicebook {
    all n : Nicebook | invariant[n]
} for 10 but exactly 4 User
