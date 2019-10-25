// Project: Project 1
// Team: Team 5
// Model for system: Nicebook

/** File Description **/
// funtions.als: containing the functions including:
//   - task 2 viewable function
//   - all helper functions

open nicebook

/** Helper Functions **/
// Return user himself / herself
fun getOnlyMe[u : User] : set User{
    u
}

// Return user's friends and himself / herself
fun getFriends[n : Nicebook, u : User] : set User {
    n.friends[u] + u
}

// Return user's friends' friends and himself / herself
fun getFriendsOfFriends[n : Nicebook, u : User] : set User {
    n.friends[u] + n.friends[n.friends[u]] + u
}

// Return everyone who is either in a friendship in the Nicebook or has
// uploaded any contents in the Nicebook.
fun getEveryone[n : Nicebook] : set User {
    n.friends.User + n.posts.Content
}

// Return the default content privacy on the publishable contents if
// it is a new content that has never been uploaded. The default privacy
// level is "levelFriends" (1)
fun getDefaultPublishPrivacy : one PrivacyLevel {
    {
        pl : PrivacyLevel |
            pl.level = levelFriends
    }
}

// Given the 2 users, u1 and u2,
// return the relation between them in Int defined in the privacy.
fun relation[u1, u2 : User, n : Nicebook] : Int {
    u1 in getOnlyMe[u2] => levelOnlyMe
    else u1 in getFriends[n, u2] => levelFriends
    else u1 in getFriendsOfFriends[n, u2] => levelFriendsOfFriends
    else levelEveryone
}

// Return all the users to the given content by its privacy level.
fun getUsersByContentPrivacy[n : Nicebook, c : Content] : set User {
    let pl = c.contentPrivacy.level, u = n.posts.c |
        pl = levelOnlyMe => getOnlyMe[u]
        else pl = levelFriends => getFriends[n, u]
        else pl = levelFriendsOfFriends => getFriendsOfFriends[n, u]
        else getEveryone[n]
}

/** Task 2: Privacy Functions **/
// 1. If the privacy level of the wall is more open than the relation
//    between u and u1, only then u can view any contents on the u1's
//    wall.
// 2. If the privacy level of the content is more open than the relation
//    between the onwer of the content and u, then the content is 
//    viewable.
fun viewable[n : Nicebook, u : User] : set Content {
    {
        c : Content |
            all u1 : User |
                owner.u1.wallPrivacy.level >= relation[u, u1, n] and
                c.contentPrivacy.level >= relation[u, n.posts.c, n]
    }
}