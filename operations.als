// Project: Project 1
// Team: Team 5
// Model for system: Nicebook   

open nicebook
open functions

/** Operations **/
// upload Note Publishable
pred upload[n, n' : Nicebook, u : User, note : Note, pl : PrivacyLevel] {
    /** pre condition **/
    all u : User | note not in n.posts[u]

    /** frame condition **/
    n'.tags = n.tags
    n'.friends = n.friends

    // promotion


    /** post condition **/
    note.contentPrivacy = pl // Set privacy for Note
    all p : note.photo | p.contentPrivacy = pl // Set privacy for all attached photos to note
    n'.posts = n.posts + u -> note
}

//upload Photo Publishable
pred upload[n, n' : Nicebook, u : User, p : Photo, pl : PrivacyLevel] {
    /** pre condition **/
    all u : User | p not in n.posts[u]

    /** frame condition **/
    n'.tags = n.tags
    n'.friends = n.friends

    // promotion


    /** post condition **/
    p.contentPrivacy = pl
    n'.posts = n.posts + u -> p
}

// Upload Comment
pred upload[n, n' : Nicebook, u : User, c : Comment] {
    /** pre condition **/
    all u : User | c not in n.posts[u]

    /** frame condition **/
    n'.tags = n.tags
    n'.friends = n.friends

    /** post condition **/
    n'.posts = n.posts + u -> c
}

pred remove[n, n' : Nicebook, u : User, c : Content] {
    /** pre condition **/
    u -> c in n.posts

    /** frame condition **/
    n'.tags = n.tags
    n'.friends = n.friends

    /** post condition **/
    n'.posts = n.posts - u -> c
}

// Publish for Note Publishable
pred publish[n, n' : Nicebook, note, note' : Note, u : User] {
    /** pre condition **/
    // 1. the publishable content is not yet published
    #note.wall = 0
    // 2. if a publishable content is not uploaded,
    //    then upload it and assign it with default wall privacy level
    u -> note not in n.posts implies upload[n, n', u, note, getDefaultPublishPrivacy]

    /** frame condition **/
    n'.friends = n.friends
    n'.tags = n.tags

    /** post condition **/
    note'.wall = note.wall + owner.u
}

//Publish for Photo Publishable
pred publish[n, n' : Nicebook, p, p' : Photo, u : User] {
    /** pre condition **/
    // 1. the publishable content is not yet published
    #p.wall = 0
    // 2. if a publishable content is not uploaded,
    //    then upload it and assign it with default wall privacy level
    u -> p not in n.posts implies upload[n, n', u, p, getDefaultPublishPrivacy]

    /** frame condition **/
    n'.friends = n.friends
    n'.tags = n.tags

    /** post condition **/
    p'.wall = p.wall + owner.u
}

pred unpublish[n, n' : Nicebook, p, p' : Publishable, u : User] {
    /** pre condition **/
    // the publishable content should be present on user's wall
    u in p.wall.owner

    /** frame condition **/
    n'.friends = n.friends
    n'.posts = n.posts
    n'.tags = n.tags

    /** post condition **/
    p'.wall = p.wall - owner.u
}

// Overloaded function for adding the comment to a Publishable
pred addComment[n, n', n'' : Nicebook, p, p' : Publishable, cm : Comment] {
    /** pre condition **/
    // Check the privacy of the comment c and see 
    // if n.posts.cm(Person who owns the comment) belongs in this
    // comment has already been uploaded by user
    #n.posts.cm = 1 and (
        (
            p.contentPrivacy.level = levelOnlyMe and
            n.posts.cm = n.posts.p
        ) or (
            p.contentPrivacy.level = levelFriends and
            n.posts.cm in getFriends[n, n.posts.p]
        ) or (
            p.contentPrivacy.level = levelFriendsOfFriends and
            n.posts.cm in getFriendsOfFriends[n, n.posts.p]
        ) or (
            p.contentPrivacy.level = levelEveryone and
            n.posts.cm in getEveryone[n]
        )
    )
    // the comment has not been added to any content
    all content : Content |
        cm not in content.comments
    // the publishable must have been published on the wall
    #p.wall > 0

    /** frame condition **/
    n'.friends = n.friends
    n'.tags = n.tags
    n''.friends = n'.friends
    n''.tags = n'.tags
    p'.wall = p.wall
    p'.contentPrivacy = p.contentPrivacy

    /** post condition **/
    //The comment inherits the privacy level of the parent
    cm.contentPrivacy = p.contentPrivacy

    p'.comments = p.comments + cm
    
    // promotion
    // publishable already uploaded
    let pu = n.posts.p | 
        n'.posts = n.posts - pu -> p and
        n''.posts = n'.posts + pu -> p'
}

// Overloaded function for adding the comment to a Comment
pred addComment[n, n', n'' : Nicebook, c, c', cm : Comment] {
    /** pre condition **/
    // Check the privacy of the comment c and see 
    // if n.posts.cm(Person who owns the comment) belongs in this
    #n.posts.cm = 1 and (
        (
            c.contentPrivacy.level = levelOnlyMe and
            n.posts.cm = n.posts.c
        ) or (
            c.contentPrivacy.level = levelFriends and
            n.posts.cm in getFriends[n, n.posts.c]
        ) or (
            c.contentPrivacy.level = levelFriendsOfFriends and
            n.posts.cm in getFriendsOfFriends[n, n.posts.c]
        ) or (
            c.contentPrivacy.level = levelEveryone and
            n.posts.cm in getEveryone[n]
        )
    )
    // the comment has not been added to any content
    all content : Content |
        cm not in content.comments
    // the root publishable content must have been published on the wall
    some p : Publishable |
        p in ^comments.cm and #p.wall > 0

    /** frame condition **/
    n'.friends = n.friends
    n'.tags = n.tags
    n''.friends = n'.friends
    n''.tags = n'.tags
    c'.contentPrivacy = c.contentPrivacy

    /** post condition **/
    //The comment inherits the privacy level of the parent
    cm.contentPrivacy = c.contentPrivacy

    c'.comments = c.comments + cm
    
    // promotion
    // publishable already uploaded
    let pu = n.posts.c | 
        n'.posts = n.posts - pu -> c and
        n''.posts = n'.posts + pu -> c'
}

// Add Tag to a publishable
pred addTag[n, n' : Nicebook, p : Publishable, u : User] {
    /** pre condition **/
    // add precondition that only people who satisfy the privacy condtion can be tagged
    #n.posts.p = 1 and (
        (
            p.contentPrivacy.level = levelFriends and
            u in getFriends[n, n.posts.p]
        ) or (
            p.contentPrivacy.level = levelFriendsOfFriends and
            u in getFriendsOfFriends[n, n.posts.p]
        ) or (
            p.contentPrivacy.level = levelEveryone and
            u in getEveryone[n]
        )
    )
    // the publishable content must have been published on the owner's wall
    n.posts.p in p.wall.owner
    // also the owner cannot be tagged in his/her post
    u != n.posts.p
    // the tag should not exist already
    p -> u not in n.tags

    /** frame condition **/
    n'.friends = n.friends
    n'.posts = n.posts

    /** post condition **/
    n'.tags = n.tags + p -> u
}

// Remove Tag from publishable.
pred removeTag[n, n' : Nicebook, p : Publishable, u : User] {
    /** pre condition **/
    p -> u in n.tags

    /** frame condition **/
    n'.friends = n.friends
    n'.posts = n.posts

    /** post condition **/
    n'.tags = n.tags - p -> u
}

// Setting the privacy level of the wall.
pred setWallPrivacy[w, w' : Wall, pl : PrivacyLevel ]{
    /** pre condition **/

    /** frame condition **/
    w'.owner = w.owner

    /** post condition **/
    w'.wallPrivacy = pl
}
