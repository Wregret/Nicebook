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

pred publish[n, n' : Nicebook, p, p' : Publishable, u : User] {
    /** pre condition **/
    // 1. the publishable content is not yet published
    #p.wall = 0
    // 2. if a publishable content is not uploaded,
    //    then upload it
    u -> p not in n.posts implies upload[n, n', u, p]

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

    // frame condition
    n'.friends = n.friends
    n'.tags = n.tags
    n''.friends = n'.friends
    n''.tags = n'.tags
    p'.wall = p.wall

    // post condition
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

    // frame condition
    n'.friends = n.friends
    n'.tags = n.tags
    n''.friends = n'.friends
    n''.tags = n'.tags

    // post condition
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
assert checkUpload {
	all n, n' : Nicebook, u : User, c : Content |
		upload[n, n', u, c] and invariant[n] implies invariant[n']
}
check checkUpload

assert checkRemove {
	all n, n' : Nicebook, u : User, c : Content |
		remove[n, n', u, c] and invariant[n] implies invariant[n']
}
check checkRemove

assert checkUploadThenRemove {
	all n, n', n'' : Nicebook, u : User, c : Content |
		upload[n, n', u, c] and remove[n', n'', u, c] implies
			n = n''
}
check checkUploadThenRemove

assert checkAddTag {
	all n, n' : Nicebook, p : Publishable, u : User |
		addTag[n, n', p, u] and invariant[n] implies invariant[n']
}
check checkAddTag

assert checkRemoveTag {
	all n, n' : Nicebook, p : Publishable, u : User |
		removeTag[n, n', p, u] and invariant[n] implies invariant[n']
}
check checkRemoveTag

assert checkAddThenRemoveTag {
	all n, n', n'' : Nicebook, u : User, p : Publishable |
		addTag[n, n', p, u] and removeTag[n', n'', p, u] implies
			n = n''
}
check checkAddThenRemoveTag

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
	all, n, n', n'' : Nicebook, p, p', p'' : Publishable, u : User |
		publish[n, n', p, p', u] and unpublish[n', n'', p', p'', u] implies
			n = n'' and p = p''
}
check checkPublishAndUnpublish
