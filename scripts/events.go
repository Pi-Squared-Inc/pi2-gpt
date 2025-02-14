package scripts

import (
	"context"
	"fmt"
	"log"
	"os"
	"scraper/common"
	"scraper/generated"
)

func ScrapeEvents(app *common.App) {
	ctx := context.Background()

	resp, err := generated.Events(ctx, *app.Client)
	if err != nil {
		log.Fatal(err)
	}

	// Create or open markdown file
	file, err := os.OpenFile("events.md", os.O_WRONLY|os.O_CREATE|os.O_TRUNC, 0644)
	if err != nil {
		log.Fatal(err)
	}
	defer file.Close()

	// Write markdown header
	file.WriteString("# Pi2 Events\n\n")

	// Iterate over events and write markdown formatted data
	for _, event := range resp.Events {
		// Create a sub-heading for each event
		file.WriteString(fmt.Sprintf("## %s\n\n", event.Data.Attributes.Name))
		file.WriteString(fmt.Sprintf("**Location:** %s\n\n", event.Data.Attributes.Location))
		if !event.Data.Attributes.Start_date.IsZero() {
			file.WriteString(fmt.Sprintf("**Start Date:** %s\n\n", event.Data.Attributes.Start_date.Format("2006-01-02")))
		}

		// Write activities information
		if len(event.Data.Attributes.Activities) > 0 {
			file.WriteString("### Activities\n\n")
			for _, activity := range event.Data.Attributes.Activities {
				file.WriteString(fmt.Sprintf("#### %s\n\n", activity.Data.Attributes.Title))
				file.WriteString(fmt.Sprintf("**Type:** %s\n\n", activity.Data.Attributes.Type))
				if activity.Data.Attributes.Abstract != "" {
					file.WriteString(fmt.Sprintf("**Abstract:**\n%s\n\n", activity.Data.Attributes.Abstract))
				}
				if activity.Data.Attributes.Presentationtitle != "" {
					file.WriteString(fmt.Sprintf("**Presentation Title:** %s\n\n", activity.Data.Attributes.Presentationtitle))
				}
				if activity.Data.Attributes.Materials != "" {
					file.WriteString(fmt.Sprintf("**Materials:** %s\n\n", activity.Data.Attributes.Materials))
				}
				if !activity.Data.Attributes.Start_date.IsZero() {
					file.WriteString(fmt.Sprintf("**Start Date:** %s\n\n", activity.Data.Attributes.Start_date.Format("2006-01-02")))
				}

				// Write recordings information
				if len(activity.Data.Attributes.Recordings) > 0 {
					file.WriteString("**Recordings:**\n\n")
					for _, recording := range activity.Data.Attributes.Recordings {
						file.WriteString(fmt.Sprintf("- [%s](%s)\n", recording.Name, recording.Url))
					}
					file.WriteString("\n")
				}

				// Write speakers information
				if len(activity.Data.Attributes.Speakers) > 0 {
					file.WriteString("**Speakers:**\n\n")
					for _, speaker := range activity.Data.Attributes.Speakers {
						file.WriteString(fmt.Sprintf("- %s (%s)\n", speaker.Data.Attributes.Name, speaker.Data.Attributes.Title))
					}
					file.WriteString("\n")
				}
			}
		}
		file.WriteString("---\n\n") // Separator between events
	}
}
