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

// }
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
// check checkUpload

assert checkRemove {
	all n, n' : Nicebook, u : User, c : Content |
		remove[n, n', u, c] and invariant[n] implies invariant[n']
}
//check checkRemove

assert checkUploadThenRemove {
	all n, n', n'' : Nicebook, u : User, c : Content |
		upload[n, n', u, c] and remove[n', n'', u, c] implies
			n = n''
}
//check checkUploadThenRemove

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
