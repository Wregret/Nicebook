// Project: Project 1
// Team: Team 5
// Model for system: Nicebook

/** File Description **/
// asertions.als: containing the assertions and checks

open nicebook
open functions
open operations

/** Assertion **/
// check if uploading a note preserves the invariant
assert checkUploadNote {
	all n, n' : Nicebook, u : User, note : Note, pl : PrivacyLevel |
		invariant[n] and upload[n, n', u, note, pl] implies invariant[n']
}
check checkUploadNote

// check if uploading a photo preserves the invariant
assert checkUploadPhoto {
    all n, n' : Nicebook, u : User, p : Photo, pl : PrivacyLevel |
		invariant[n] and upload[n, n', u, p, pl] implies invariant[n']
}
check checkUploadPhoto

// check if uploading a comment preserves the invariant
assert checkUploadComment {
    all n, n' : Nicebook, u : User, c : Comment |
		invariant[n] and upload[n, n', u, c] implies invariant[n']
}
check checkUploadComment

// check if removing a note preserves the invariant
assert checkRemoveNote {
	all n, n' : Nicebook, u : User, note : Note |
		invariant[n] and remove[n, n', u, note] implies invariant[n']
}
check checkRemoveNote

// check if removing a note preserves the invariant
assert checkRemovePhoto {
	all n, n' : Nicebook, u : User, p : Photo |
		invariant[n] and remove[n, n', u, p] implies invariant[n']
}
check checkRemovePhoto

// check if removing a note preserves the invariant
assert checkRemoveComment {
	all n, n' : Nicebook, u : User, cm : Comment |
		invariant[n] and remove[n, n', u, cm] implies invariant[n']
}
check checkRemoveComment

// check if adding a tag preserves the invariant
assert checkAddTag {
	all n, n' : Nicebook, p : Publishable, u : User |
		invariant[n] and addTag[n, n', p, u] implies invariant[n']
}
check checkAddTag

// check if removing a tag preserves the invariant
assert checkRemoveTag {
	all n, n' : Nicebook, p : Publishable, u : User |
		invariant[n] and removeTag[n, n', p, u] implies invariant[n']
}
check checkRemoveTag

// check if adding and removing a content get the same state for Nicebook
assert checkAddThenRemoveTag {
	all n, n', n'' : Nicebook, u : User, p : Publishable |
		invariant[n] and 
		addTag[n, n', p, u] and 
		removeTag[n', n'', p, u] implies
		(invariant[n'] and n = n'')
}
check checkAddThenRemoveTag

// check if adding a comment preserves the invariant
assert checkAddComment {
	// check adding a comment to a publishable
    all n, n', n'' : Nicebook, p, p' : Publishable, cm : Comment |
        invariant[n] and addComment[n, n', n'', p, p', cm] implies invariant[n']
	// check adding a comment to a comment
    all n, n', n'' : Nicebook, c, c' : Comment, cm : Comment |
        invariant[n] and addComment[n, n', n'', c, c', cm] implies invariant[n']
}
check checkAddComment

// check publishing a note to a publishable content preserves the invariant
assert checkPublishNote {
	// check publishing a note
	all n, n' : Nicebook, note, note' : Note, u : User |
		invariant[n] and publish[n, n', note, note', u] implies invariant[n']
	// check publishing a photo
	all n, n' : Nicebook, p, p' : Photo, u : User |
		invariant[n] and publish[n, n', p, p', u] implies invariant[n']
}
check checkPublishNote

// check publishing a note to a publishable content preserves the invariant
assert checkUnpublish {
	all n, n' : Nicebook, p, p' : Publishable, u : User |
		invariant[n] and unpublish[n, n', p, p', u] implies invariant[n']
}
check checkUnpublish


/** Task 2: Privacy Violation **/
// If the Nicebook is valid one AND the content is viewable to the given
// user, then this user must be allowed by the content privacy level to
// view.
assert noPrivacyViolation {
    all n : Nicebook, u : User, c : Content |
        (invariant[n] and c in viewable[n, u]) implies
        u in getUsersByContentPrivacy[n, c]
}
check noPrivacyViolation
