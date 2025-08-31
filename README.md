# GrandFantasia-ChatLogger
This is a Viewer and Analyser for the Game Grand Fantasia based on its Chat

<img width="1127" height="1271" alt="2025-08-24-23 19-57" src="https://github.com/user-attachments/assets/5f431a25-c48f-494e-892a-afb910b18de8" />

## Features
- **Real-time Chat Logging**
- **Per-Scan Deduplication**: Prevents identical messages from being logged multiple times within a single scan cycle, while correctly logging repeated messages from different cycles.
- **Customizable UI**:
  - Set a fixed window size (1300x1000 by default) that is always on top.
  - Customize font size and channel-specific text colors.
  - Filter messages by predefined channels or user-created groups.
- **Advanced Analytics**:
  - Damage Analyzer: Tracks and displays the highest damage dealt by skill, highest normal attacks, and top damage against specific targets over various timeframes (5 min, 10 min, 60 min, 24 hours).
  - Experience Analyzer: Tracks and displays total and average experience gains for normal EXP, specialization EXP, mount EXP, and mastery EXP over multiple timeframes.
- **Audio Notifications**: Play custom sound files or a default ding for messages in specific channels or sub-channels.
- **Robust Logging**: Messages are logged to a **chat_log.txt** file, which automatically truncates to a user-defined size limit to prevent it from growing too large.

