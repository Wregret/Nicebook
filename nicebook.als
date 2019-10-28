// Project: Project 1
// Team: Team 5
// Model for system: Nicebook

open privacy

/** Signatures **/
// Signature of Nicebook.
sig Nicebook {
    posts : User -> some Content,   // Contents created by users
    friends : set User -> set User, // Friendships between users
    tags : Publishable -> some User // Tags from publishable contents to users
}

// Signature of User.
sig User {}

// Signature of Wall.
sig Wall {
    owner : one User,               // The user who owns the wall.
    wallPrivacy : one PrivacyLevel  // The privacy level of the wall.
}

// Abstract signature of Content.
abstract sig Content {
    contentPrivacy : one PrivacyLevel,  // The privacy level of the content.
    comments : set Comment              // The set of the comments added to the content.
}

// Abstract signature of Publishable Content.
abstract sig Publishable extends Content {
    wall : set Wall                 // The set of wall that this publishable content can be published on.
}

// Signature of Note which extends Publishable Content.
sig Note extends Publishable {
    photo : set Photo,              // The set of photos that are included in the note.
}

// Signature of Photo which extends Publishable Content.
sig Photo extends Publishable {}

// Signature of Comment which extends Content.
sig Comment extends Content {}

/** Invairants **/
/** Signature Invariant **/
// Invariant for Comment
pred commentInvariant[c : Comment] {
    noSelfComment[c]                // No comment can be added to itself.
    noOrphanComment[c]              // The comment must be attached to some 
}

// Invariant for Content
pred contentInvariant[n : Nicebook] {
    // a content must be owned by one user
    all c : Content |
        #n.posts.c = 1
}

// Invariant for Wall
pred wallInvariant[n : Nicebook] {
    // Every user has his / her unique wall.
    all w1, w2 : Wall |
        w1 != w2 implies w1.owner != w2.owner
    // A user must own a wall.
    all u : User |
        #owner.u = 1
    // All publishable contents on any wall must have been uploaded.
    all p : Publishable |
        #p.wall > 0 implies #n.posts.p = 1
}

/** Mapping Invariant **/
// Aggregated friendship invariant.
pred friendshipInvariant[n : Nicebook] {
    noSelfFriendship[n]
    sysmetricFriendship[n]
}

// Invariant for tags
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

/** Helper Invariant **/
// No user be a friend with himself.
pred noSelfFriendship[n : Nicebook] {
    no iden & n.friends
}

// Sysmetric friendship
pred sysmetricFriendship[n : Nicebook] {
    all u1, u2 : User |
        u1 in n.friends[u2] implies u2 in n.friends[u1]
}

// No comment can comment itself.
// No circular comments.
pred noSelfComment[c : Comment] {
    c not in c.^comments
}

// A comment must be associated to a note or a photo or another comment
pred noOrphanComment[c : Comment] {
    some p : Publishable |
        c in p.comments
    or
    some comment : Comment |
        c in comment.comments and c != comment
}

// Total invariant
pred invariant[n : Nicebook] {
    friendshipInvariant[n] and
    contentInvariant[n] and
    wallInvariant[n] and
    tagInvariant[n]
    all c : Comment |
        commentInvariant[c]
}
