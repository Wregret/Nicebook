// Project: Project 1
// Team: Team 5
// Model for system: Nicebook

// NOTE: this file defines the privacy level as constants

let levelOnlyMe = 0
let levelFriends = 1
let levelFriendsOfFriends = 2
let levelEveryone = 3

sig PrivacyLevel {
    level : one Int
}{
    level >= levelOnlyMe and
    level <= levelEveryone
}