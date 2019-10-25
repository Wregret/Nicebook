// Project: Project 1
// Team: Team 5
// Model for system: Nicebook

open nicebook
open functions
open operations

/** Assertion **/
assert checkUploadNote {
	all n, n' : Nicebook, u : User, note : Note, pl : PrivacyLevel |
		upload[n, n', u, note, pl] and invariant[n] implies invariant[n']
}
check checkUploadNote

assert checkUploadPhoto {
    all n, n' : Nicebook, u : User, p : Photo, pl : PrivacyLevel |
		upload[n, n', u, p, pl] and invariant[n] implies invariant[n']
}
check checkUploadPhoto

assert checkUploadComment {
    all n, n' : Nicebook, u : User, c : Comment |
		upload[n, n', u, c] and invariant[n] implies invariant[n']
}
check checkUploadComment

assert checkRemove {
	all n, n' : Nicebook, u : User, c : Content |
		remove[n, n', u, c] and invariant[n] implies invariant[n']
}
check checkRemove

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

assert checkPublishNote {
	all n, n' : Nicebook, note, note' : Note, u : User |
		publish[n, n', note, note', u] and invariant[n] implies invariant[n']
}
check checkPublishNote

assert checkUnpublish {
	all n, n' : Nicebook, p, p' : Publishable, u : User |
		unpublish[n, n', p, p', u] and invariant[n] implies invariant[n']
}
check checkUnpublish

assert checkPublishAndUnpublishNote {
	all n, n', n'' : Nicebook, note, note', note'' : Note, u : User |
		(publish[n, n', note, note', u] and unpublish[n', n'', note', note'', u]) implies
		n = n''
}
check checkPublishAndUnpublishNote

assert noPrivacyViolation {
    all n : Nicebook, u : User, c : Content |
        (
            u = n.posts.c or
            u in n.tags[c]
        ) implies c in viewable[n, u]
}
check noPrivacyViolation