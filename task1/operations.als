// Project: Project 1
// Team: Team 5
// Model for system: Nicebook   

open nicebook
open functions

/** Operations **/
// upload Note Publishable
pred upload[n, n' : Nicebook, u : User, note : Note, pl : PrivacyLevel] {
    // pre condition
    u -> note not in n.posts

    // frame condition
    n'.tags = n.tags
    n'.friends = n.friends

    // promotion


    // post condition
    note.contentPrivacy = pl // Set privacy for Note
    all p : note.photo | p.contentPrivacy = pl // Set privacy for all attached photos to note
    n'.posts = n.posts + u -> note
}

//upload Photo Publishable
pred upload[n, n' : Nicebook, u : User, p : Photo, pl : PrivacyLevel] {
    // pre condition
    u -> p not in n.posts

    // frame condition
    n'.tags = n.tags
    n'.friends = n.friends

    // promotion


    // post condition
    p.contentPrivacy = pl
    n'.posts = n.posts + u -> p
}

// Upload Comment
pred upload[n, n' : Nicebook, u : User, c : Comment] {
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

pred addComment[n, n', n'' : Nicebook, p, p' : Publishable, cm : Comment] {
    /** pre condition **/
    // comment has already been uploaded by user
    #n.posts.cm = 1
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

pred addComment[n, n', n'' : Nicebook, c, c', cm : Comment] {
    /** pre condition **/
    // comment has already been uploaded by user
    #n.posts.cm = 1
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

pred addTag[n, n' : Nicebook, p : Publishable, u : User] {
    // pre condition
    p -> u not in n.tags

    // frame condition
    n'.friends = n.friends
    n'.posts = n.posts

    // post condition
    n'.tags = n.tags + p -> u
}

pred removeTag[n, n' : Nicebook, p : Publishable, u : User] {
    // pre condition
    p -> u in n.tags

    // frame condition
    n'.friends = n.friends
    n'.posts = n.posts

    // post condition
    n'.tags = n.tags - p -> u
}

/** Assertion **/
assert checkUploadNote {
	all n, n' : Nicebook, u : User, note : Note, pl : PrivacyLevel |
		upload[n, n', u, note, pl] and invariant[n] implies invariant[n']
}
//check checkUploadNote

assert checkUploadPhoto {
    all n, n' : Nicebook, u : User, p : Photo, pl : PrivacyLevel |
		upload[n, n', u, p, pl] and invariant[n] implies invariant[n']
}
//check checkUploadPhoto

assert checkUploadComment {
    all n, n' : Nicebook, u : User, c : Comment |
		upload[n, n', u, c] and invariant[n] implies invariant[n']
}
//check checkUploadComment

assert checkRemove {
	all n, n' : Nicebook, u : User, c : Content |
		remove[n, n', u, c] and invariant[n] implies invariant[n']
}
//check checkRemove

assert checkAddTag {
	all n, n' : Nicebook, p : Publishable, u : User |
		addTag[n, n', p, u] and invariant[n] implies invariant[n']
}
//check checkAddTag

assert checkRemoveTag {
	all n, n' : Nicebook, p : Publishable, u : User |
		removeTag[n, n', p, u] and invariant[n] implies invariant[n']
}
//check checkRemoveTag

assert checkAddThenRemoveTag {
	all n, n', n'' : Nicebook, u : User, p : Publishable |
		addTag[n, n', p, u] and removeTag[n', n'', p, u] implies
			n = n''
}
//check checkAddThenRemoveTag

assert checkAddComment {
    all n, n', n'' : Nicebook, p, p' : Publishable, cm : Comment |
        addComment[n, n', n'', p, p', cm] and invariant[n] implies invariant[n']
    all n, n', n'' : Nicebook, c, c' : Comment, cm : Comment |
        addComment[n, n', n'', c, c', cm] and invariant[n] implies invariant[n']
}
check checkAddComment

assert checkPublish {
	all n, n' : Nicebook, p, p' : Publishable, u : User |
		publish[n, n', p, p', u] and invariant[n] implies invariant[n']
}
check checkPublish

assert checkUnpublish {
	all n, n' : Nicebook, p, p' : Publishable, u : User |
		unpublish[n, n', p, p', u] and invariant[n] implies invariant[n']
}
check checkUnpublish

assert checkPublishAndUnpublish {
	all n, n', n'' : Nicebook, p, p', p'' : Publishable, u : User |
		(publish[n, n', p, p', u] and unpublish[n', n'', p', p'', u]) implies
		n = n''
}
check checkPublishAndUnpublish
