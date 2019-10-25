// Project: Project 1
// Team: Team 5
// Model for system: Nicebook

open nicebook

/** Helper Functions **/
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

fun getDefaultPublishPrivacy : one PrivacyLevel {
    {
        pl : PrivacyLevel |
            pl.level = levelFriends
    }
}

fun relation[u1, u2 : User, n : Nicebook] : Int {
    u1 in getOnlyMe[u2] => levelOnlyMe
    else u1 in getFriends[n, u2] => levelFriends
    else u1 in getFriendsOfFriends[n, u2] => levelFriendsOfFriends
    else levelEveryone
}

/** Task 2: Privacy Functions **/
fun viewable[n : Nicebook, u : User] : set Content {
    // 1. if the privacy level of the wall is more open than the relation
    //    between u and u1, only then u can view any contents on the u1's
    //    wall
    // 2. if the privacy level of the content is more open than the relation
    //    between the onwer of the content and u, then the content is 
    //    viewable
    {
        c : Content |
            all u1 : User |
                owner.u1.wallPrivacy.level >= relation[u, u1, n] and
                c.contentPrivacy.level >= relation[u, n.posts.c, n]
    }
}