// Project: Project 1
// Team: Team 5
// Model for system: Nicebook

open nicebook

/** Functions **/
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