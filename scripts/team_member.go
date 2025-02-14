package scripts

import (
	"context"
	"fmt"
	"log"
	"os"
	"scraper/common"
	"scraper/generated"
)

func ScrapeTeamMembers(app *common.App) {
	ctx := context.Background()

	resp, err := generated.TeamMembers(ctx, *app.Client)
	if err != nil {
		log.Fatal(err)
	}

	// Create or open markdown file
	file, err := os.OpenFile("team_members.md", os.O_WRONLY|os.O_CREATE|os.O_TRUNC, 0644)
	if err != nil {
		log.Fatal(err)
	}
	defer file.Close()

	// Write markdown header
	file.WriteString("# Pi2 Team Members\n\n")

	// Iterate over team members and write markdown formatted data
	for _, teamMember := range resp.TeamMembers {
		// Create a sub-heading for each member
		file.WriteString(fmt.Sprintf("## %s\n\n", teamMember.Data.Attributes.Name))
		file.WriteString(fmt.Sprintf("**Title:** %s\n\n", teamMember.Data.Attributes.Title))
		file.WriteString(fmt.Sprintf("**Bio:**\n%s\n\n", teamMember.Data.Attributes.Bio))
		file.WriteString("---\n\n") // Separator
	}
}
