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

/** Privacy Functions **/
fun viewable[n : Nicebook, u : User] : set Content {
    // 1. all the contents owned by the user are viewable to him / her
    // 2. all the contents pulished on his / her friends' wall whose privacy
    //    levels are levelFriends
    // 3. all the contents pulished on his / her friends' friends' wall whose
    //    privacy levels are levelFriends
    // 4. all the contents pulished with privacy level as levelEveryone
    n.posts[u] + 
    { 
        c : n.posts[getFriends[n, u]] |
            c.contentPrivacy.level = levelFriends
    } + { 
        c : n.posts[getFriendsOfFriends[n, u]] |
            c.contentPrivacy.level = levelFriendsOfFriends 
    } + {
        c : n.posts[User] |
            c.contentPrivacy.level = levelEveryone
    }
}